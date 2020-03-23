(ns floor.compiler
  (:require
    [boot.prelude :as p :refer [p]]
    [boot.generics :as g :refer [generic]]
    [floor.compiler.lambda :as lambda]
    [floor.compiler.bindings :as bindings]
    [floor.compiler.expansion :as exp]))

(def global-env (atom {}))

(do :expanders

    (defn IF_form
      ([test then]
       (if (symbol? test)
         `(if (floor.core/success? ~test) ~then ~test)
         `(let [t# ~test]
            (if (floor.core/success? t#) ~then t#))))
      ([test then else]
       (if else
         `(if (floor.core/success? ~test) ~then ~else)
         (IF_form test then)))
      ([test then test2 then2 & others]
       (IF_form test then (apply IF_form test2 then2 others))))

    (defn IF-expand [env args]
      (apply IF_form (map (partial exp/expand env) args)))

    (defn CS_compile-case [env bs expr options]
      (let [bs (bindings/bindings bs options)
            bs (if (:unified options) (bindings/unified bs) bs)
            {:keys [env bindings]} (bindings/optimize env bs)
            expr (exp/expand env expr)]
        (if-not (seq bindings)
          expr
          (loop [ret expr
                 [[p1 e1] & pes :as bs]
                 (reverse (partition 2 bindings))]
            (if-not (seq bs)
              ret
              (recur `(let [~p1 ~e1] (if (floor.core/success? ~p1) ~ret ~p1))
                     pes))))))

    (defn CS_mk [options]
      {:expand (fn CS_expand
                 [env [verb b1 e1 & more :as form]]
                 (let [exp (p exp/expand env)]
                   (condp = (count form)
                     1 nil
                     2 (exp b1) #_(CS_wrap-return (exp b1) options)
                     3 (cond
                         (not (vector? b1)) (IF-expand env [b1 e1])
                         :else (CS_compile-case env b1 e1 options))
                     ;else
                     `(let [a# ~(CS_expand env [verb b1 e1])]
                        (if (floor.core/success? a#)
                          a# ~(CS_expand env (cons verb more)))))))})

    (defn LAMBDA_mk [binding-form]
      {:expand (fn [env form]
                 (exp/expand env (lambda/compile binding-form (lambda/parse (next form)))))})

    (defn LAMBDA_definition [binding-form]
      {:expand (fn [env form]
                 (let [{:as parsed :keys [name doc]} (lambda/parse (next form))]
                   `(def ~name
                      ~@(when doc [doc])
                      ~(exp/expand env (lambda/compile binding-form parsed)))))})


    (defn GENERIC_mk [verb]
      {:expand (fn [env form]
                 (exp/expand env `(verb ~@(lambda/wrap-generic-body (next form)))))})

    (defn CASE_expand [{:keys [binding-form seed cases]}]
      (let [patterns (take-nth 2 cases)
            exprs (take-nth 2 (next cases))
            seed-sym (gensym "seed_")]
        `(let [~seed-sym ~seed]
           (~binding-form
             ~@(interleave (map (fn [p] [p seed-sym]) patterns)
                           exprs)))))

    (defn CASE_mk [binding-form]
      {:expand (fn [env [_ seed & cases]]
                 (exp/expand env (CASE_expand {:cases cases :seed seed :binding-form binding-form})))}))

(do :macros

    (swap! global-env
           update
           'floor.core
           merge
           {'cs (CS_mk {})
            'csu (CS_mk {:unified true})
            '?cs (CS_mk {:binding-mode :opt})
            '!cs (CS_mk {:binding-mode :strict})
            '?csu (CS_mk {:binding-mode :opt :unified true})
            '!csu (CS_mk {:binding-mode :strict :unified true})

            'f (LAMBDA_mk 'floor.core/cs)
            'fu (LAMBDA_mk 'floor.core/csu)
            '!f (LAMBDA_mk 'floor.core/!cs)
            '!fu (LAMBDA_mk 'floor.core/!csu)
            '?f (LAMBDA_mk 'floor.core/?cs)
            '?fu (LAMBDA_mk 'floor.core/?csu)

            'case (CASE_mk 'floor.core/cs)
            'casu (CASE_mk 'floor.core/csu)

            'deff (LAMBDA_definition 'floor.core/cs)
            'defu (LAMBDA_definition 'floor.core/csu)

            'defg (GENERIC_mk 'boot.generics/generic)
            'generic+ (GENERIC_mk 'boot.generics/generic+)
            'defrg (GENERIC_mk 'boot.generics/reduction)})

    (defmacro import-top-level-form [s]
      (let [unqual-sym (symbol (name s))]
        `(defmacro ~unqual-sym [~'& xs#]
           (exp/expand @global-env (cons '~s xs#)))))

    (defmacro import-core-macros []
      `(do ~@(map (fn [s] `(import-top-level-form ~(symbol "floor.core" (name s))))
                  (keys (get @global-env 'floor.core))))))

(comment :scratch

         (exp/expand @global-env
                     '(floor.core/csu [[a b] x] :a [1 x a 2 a 3] :b))

         (exp/expand @global-env
                     '(floor.core/csu [1 x a x a y] [a x (floor.core/f [z] (+ y a z))]))

         (import-top-level-form floor.core/csu)

         (import-core-macros)

         (macroexpand '(csu [1 x a x a y] [a x (f [z] (+ y a z))]))

         (macroexpand '(csu [a 1 a 2] :iop :nop)))