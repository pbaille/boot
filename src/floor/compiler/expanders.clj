(ns floor.compiler.expanders
  (:require [floor.compiler.env :as env]
            [floor.compiler.bindings :as bindings]
            [floor.compiler.lambda :as lambda]))

(defn if-form
  ([test then]
   (if (symbol? test)
     `(if (floor.core/success? ~test) ~then ~test)
     `(let [t# ~test]
        (if (floor.core/success? t#) ~then t#))))
  ([test then else]
   (if else
     `(if (floor.core/success? ~test) ~then ~else)
     (if-form test then)))
  ([test then test2 then2 & others]
   (if-form test then (apply if-form test2 then2 others))))

(defn if-expand [env args]
  (apply if-form (map (partial env/expand env) args)))

;; conditional bindings

(defn cs-return [ret else]
  (let [retsym (gensym)]
    `(let [~retsym ~ret]
       (if (floor.core/success? ~retsym)
         (get ~retsym ::cs-return)
         ~(if (::void else) retsym else)))))

(defn cs-test-case [env test then else]
  (let [retsym (gensym)]
    `(let [~retsym ~(env/expand env test)]
       (if (floor.core/success? ~retsym)
         ~(cs-return (env/expand env then)
                     (if (::void else) ~retsym (env/expand env else)))
         ~retsym))))

(defn cs-binding-case [env bs expr else options]
  (let [bs (bindings/bindings bs options)
        bs (if (:unified options) (bindings/unified bs options) bs)
        {:keys [env bindings]} (bindings/optimize env bs)
        expr (env/expand env expr)]
    (if-not (seq bindings)
      (cs-return expr else)
      (loop [ret expr
             [[p1 e1] & pes :as bs]
             (reverse (partition 2 bindings))]
        (if-not (seq bs)
          (cs-return ret else)
          (recur `(let [~p1 ~e1] (if (floor.core/success? ~p1) ~ret ~p1))
                 pes))))))

(defn cs-mk [options]
  {:expand (fn cs-expand
             [env [verb b1 e1 & more :as form]]
             (cond
               (not more)
               (cs-expand env [verb b1 e1 {::void true}])

               (not (next more))
               (if (not (vector? b1))
                 (cs-test-case env b1 {::cs-return e1} (first more))
                 #_(if-expand env [b1 {::cs-return e1} (first more)])
                 (cs-binding-case env b1 {::cs-return e1} (first more) options))

               :else
               (cs-expand env [verb b1 e1 (cs-expand env (cons verb more))])))})

(defn let-mk [binding-form]
  {:expand (fn [env form]
             (env/expand env (list binding-form (second form) (list* 'do (drop 2 form)))))})

;; lambdas and friends

(defn lambda-mk [binding-form]
  {:expand (fn [env form]
             (env/expand env (lambda/compile binding-form (lambda/parse (next form)))))})

(defn lambda-definition [binding-form]
  {:expand (fn [env form]
             (let [{:as parsed :keys [name doc]} (lambda/parse (next form))]
               `(def ~name
                  ~@(when doc [doc])
                  ~(env/expand env (lambda/compile binding-form parsed)))))})

(defn unary-lambda-mk [binding-form]
  {:expand (fn [env form]
             (let [name? (even? (count form))
                   cases (if name? (drop 2 form) (next form))
                   lambda-cases (interleave (map vector (take-nth 2 cases)) (take-nth 2 (next cases)))
                   lambda-form (concat (take (if name? 2 1) form) lambda-cases)
                   lambda-expander (:expand (lambda-mk binding-form))]
               (lambda-expander env lambda-form)))})

(defn generic-mk [verb]
  {:expand (fn [env form]
             (env/expand env (cons verb (lambda/wrap-generic-body (next form)))))})

(def thing
  {:expand (fn [env [_ & impls]]
             `(g/thing
                ~@(map (fn [[name & body]]
                         (->> (lambda/parse body)
                              (lambda/compile 'floor.core/cs)
                              (env/expand env)
                              (cons name)))
                       impls)))})

;; case

(defn case-expand [{:keys [binding-form seed cases]}]
  (let [patterns (take-nth 2 cases)
        exprs (take-nth 2 (next cases))
        seed-sym (gensym "seed_")]
    `(let [~seed-sym ~seed]
       (~binding-form
         ~@(interleave (map (fn [p] [p seed-sym]) patterns)
                       exprs)))))

(defn case-mk [binding-form]
  {:expand (fn [env [_ seed & cases]]
             (env/expand env (case-expand {:cases cases :seed seed :binding-form binding-form})))})

(comment

  ((:expand (cs-mk {})) {}
   '(cs [a 1] a [b 2] b))

  ((:expand (lambda-mk 'floor.core/cs)) {}
   '(f [a] a))

  ((:expand (lambda-definition 'floor.core/cs)) {}
   '(deff iop [a] a))

  ((:expand (cs-mk {})) {}
   '(cs [a 42] a)))


(def or-expand
  {:expand (fn self [env [v & xs]]
             (let [retsym (gensym)]
               (if xs
                 `(let [~retsym ~(env/expand env (first xs))]
                    (if (floor.core/success? ~retsym)
                      ~retsym
                      ~(if (next xs)
                         (self env (list* v (next xs)))
                         retsym)))
                 `(floor.core/failure ::or))))})

(def and-expand
  {:expand (fn self [env [v & xs]]
             (let [retsym (gensym)]
               (if xs
                 `(let [~retsym ~(env/expand env (first xs))]
                    (if (floor.core/success? ~retsym)
                      ~(if (next xs)
                         (self env (list* v (next xs)))
                         retsym)
                      ~retsym))
                 true)))})