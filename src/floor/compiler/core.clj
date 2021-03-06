(ns floor.compiler.core
  (:require
    [boot.prelude :as p :refer [p]]
    [floor.compiler.env :as env]
    [floor.compiler.expanders :as exp]
    [boot.generics :as g]
    [floor.compiler.lambda :as lambda]))

(def global-env
  (atom
    {'floor.core
     {'cs (exp/cs-mk {})
      'csu (exp/cs-mk {:unified true})
      '?cs (exp/cs-mk {:binding-mode :opt})
      '!cs (exp/cs-mk {:binding-mode :strict})
      '?csu (exp/cs-mk {:binding-mode :opt :unified true})
      '!csu (exp/cs-mk {:binding-mode :strict :unified true})

      'or exp/OR
      ;'or2 exp/OR2
      'and exp/AND

      'let (exp/let-mk 'floor.core/cs)
      '?let (exp/let-mk 'floor.core/?cs)
      '!let (exp/let-mk 'floor.core/!csu)
      'lut (exp/let-mk 'floor.core/csu)
      '?lut (exp/let-mk 'floor.core/?cs)
      '!lut (exp/let-mk 'floor.core/!csu)

      'f (exp/lambda-mk 'floor.core/cs)
      '?f (exp/lambda-mk 'floor.core/?cs)
      '!f (exp/lambda-mk 'floor.core/!cs)
      'fu (exp/lambda-mk 'floor.core/csu)
      '?fu (exp/lambda-mk 'floor.core/?csu)
      '!fu (exp/lambda-mk 'floor.core/!csu)

      'f1 (exp/unary-lambda-mk 'floor.core/cs)
      'f1u (exp/unary-lambda-mk 'floor.core/csu)

      'f_ exp/underscore-lambda

      'case (exp/case-mk 'floor.core/cs)
      'casu (exp/case-mk 'floor.core/csu)

      'deff (exp/lambda-definition 'floor.core/cs)
      'defu (exp/lambda-definition 'floor.core/csu)

      'defg exp/defg
      'generic+ (exp/generic-mk 'boot.generics/generic+)
      'defrg (exp/generic-mk 'boot.generics/reduction)}}))

(reset! g/lambda-case-compiler* lambda/compile-case)

(defmacro import-top-level-form [s]
  (let [unqual-sym (symbol (name s))]
    `(defmacro ~unqual-sym [~'& xs#]
       (env/expand @global-env (cons '~s xs#)))))

(defmacro import-core-macros []
  `(do ~@(map (fn [s] `(import-top-level-form ~(symbol "floor.core" (name s))))
              (keys (get @global-env 'floor.core)))))

(comment :scratch

         (env/expand @global-env '(floor.core/f_ (mul 2 _)))

         (env/expand @global-env '(floor.core/or 1 2 3))

         (env/expand @global-env '(floor.core/and ((car checkers) y)
                                           (recur (cdr checkers))))

         (env/expand {} '(let ~(vec (interleave '[a b] [1 2])) (+ a b)))

         (env/expand @global-env
                     '(floor.core/csu [[a b] x] :a [1 x a 2 a 3] :b))

         (env/expand @global-env
                     '(floor.core/csu [1 x a x a y] [a x (floor.core/f [z] (+ y a z))]))

         (import-top-level-form floor.core/csu)

         (import-core-macros)

         (macroexpand '(csu [1 x a x a y] [a x (f [z] (+ y a z))]))

         (macroexpand '(csu [a 1 a 2] :iop :nop))

         ((:expand (exp/unary-lambda-mk 'floor.core/cs))
          {} '(f1 me (pos? a) [:pos a] (neg? a) [:neg b] (zero? x) [:zero x] x [:any x])))