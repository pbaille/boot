(ns floor.compiler.expanders
  (:require [floor.compiler.env :as env]
            [floor.compiler.bindings :as bindings]
            [floor.compiler.lambda :as lambda]
            [boot.prelude :as p]))

(defmacro expander
  "syntax suger wrap a function in a: an expand key"
  [& body]
  (let [{:keys [name cases]} (p/parse-fn body)]
    {:expand `(fn ~name ~@cases)}))

;; conditional bindings

(defn cs-return [ret else]
  (if (::void else)
    ret
    (let [retsym (gensym)]
      `(let [~retsym ~ret]
         (if (floor.core/success? ~retsym)
           (get ~retsym ::cs-return)
           ~else)))))

(defn cs-binding-case
  [env bs expr else options]
  (let [bs (if (vector? bs) bs [(gensym "check_") bs])
        expr (if (::void else) expr {::cs-return expr})]
    (cs-return
      (bindings/compile-let-form
        {:env env :bindings bs :return expr :options options})
      (env/expand env else))))

(defn cs-mk [options]
  (expander cs-expand
            [env [verb b1 e1 & more :as form]]
            (cond
              (not more)
              (cs-expand env [verb b1 e1 {::void true}])

              (not (next more))
              (cs-binding-case
                env b1 e1 (first more) options)

              :else
              (cs-expand env [verb b1 e1 (cs-expand env (cons verb more))]))))



(defn let-mk [binding-form]
  (expander [env form]
            (env/expand env (list binding-form (second form) (list* 'do (drop 2 form))))))

;; lambdas and friends

(defn lambda-mk [binding-form]
  (expander [env form]
            (env/expand env (lambda/compile binding-form (lambda/parse (next form))))))

(defn lambda-definition [binding-form]
  (expander [env form]
            (let [{:as parsed :keys [name doc]} (lambda/parse (next form))]
              `(def ~name
                 ~@(when doc [doc])
                 ~(env/expand env (lambda/compile binding-form parsed))))))

(defn unary-lambda-mk [binding-form]
  (expander [env form]
            (let [name? (even? (count form))
                  cases (if name? (drop 2 form) (next form))
                  lambda-cases (interleave (map vector (take-nth 2 cases)) (take-nth 2 (next cases)))
                  lambda-form (concat (take (if name? 2 1) form) lambda-cases)
                  lambda-expander (:expand (lambda-mk binding-form))]
              (lambda-expander env lambda-form))))

(defn generic-mk [verb]
  (expander [env form]
            (env/expand env (cons verb (lambda/wrap-generic-body (next form))))))

(def thing
  (expander [env [_ & impls]]
            `(g/thing
               ~@(map (fn [[name & body]]
                        (->> (lambda/parse body)
                             (lambda/compile 'floor.core/cs)
                             (env/expand env)
                             (cons name)))
                      impls))))

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
  (expander [env [_ seed & cases]]
            (env/expand env (case-expand {:cases cases :seed seed :binding-form binding-form}))))


(def OR
  (expander self [env [v & xs]]
            (let [retsym (gensym)]
              (if xs
                `(let [~retsym ~(env/expand env (first xs))]
                   (if (floor.core/success? ~retsym)
                     ~retsym
                     ~(if (next xs)
                        (self env (list* v (next xs)))
                        retsym)))
                `(floor.core/failure ::or)))))

(def AND
  (expander self [env [v & xs]]
            (let [retsym (gensym)]
              (if xs
                (if (next xs)
                  `(let [~retsym ~(env/expand env (first xs))]
                     (if (floor.core/success? ~retsym)
                       ~(self env (list* v (next xs)))
                       ~retsym))
                  (env/expand env (first xs)))
                true))))

((:expand AND) {} '(and ((car checkers) y)
                        (recur (cdr checkers))))



(comment

  ((:expand (cs-mk {})) {}
   '(cs [a 1] a [b 2] b))

  ((:expand (lambda-mk 'floor.core/cs)) {}
   '(f [a] a))

  ((:expand (lambda-definition 'floor.core/cs)) {}
   '(deff iop [a] a))

  ((:expand (cs-mk {})) {}
   '(cs [a 42] a))

  (comment
    (defn cs-test [form]
      ((:expand (cs-mk {})) {} form))

    (eval (cs-test '(cs [a 1 b 2] (+ a b) [a 10 b 12] :iop)))))