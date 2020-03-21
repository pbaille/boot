(ns floor.control
  (:refer-clojure :exclude [or and])
  (:require [clojure.core :as c]
            [boot.generics :as g]
            [boot.named :as n]
            [boot.prelude :as p :refer [is]]
            [floor.declaration :as d :refer [failure]]
            [floor.utils :as u]
            [floor.compiler :as cpl]))

(def failure0 (failure ::failure))

(defn failure? [x] (g/implements? d/fail x))
(defn success? [x] (not (failure? x)))

(defn IF-form
  ([test then]
   (if (symbol? test)
     `(if (success? ~test) ~then ~test)
     `(let [t# ~test]
        (if (success? t#) ~then t#))))
  ([test then else]
   (if else
     `(if (success? ~test) ~then ~else)
     (IF-form test then)))
  ([test then test2 then2 & others]
   (IF-form test then (apply IF-form test2 then2 others))))

(defn IF-expand [env args]
  (apply IF-form (map (partial cpl/expand env) args)))

(defn QMARK-expand
  [env [b1 e1 & more :as args]]
  (let [exp (partial cpl/expand env)]
    (condp = (count args)
      0 nil
      1 (exp b1)
      2 (cond
          (not (vector? b1)) (IF-expand env [b1 e1])
          (not (seq b1)) (exp e1)
          :else
          (let [[pat expr & others] b1
                [p1 e1' & bs] (d/bindings pat (exp expr))]
            `(let ~[p1 e1']
               ~(let [env (cpl/env-shadow env p1)]
                  (IF-expand
                    env
                    [p1
                     (QMARK-expand
                       env
                       [(vec bs)
                        (if others
                          (QMARK-expand env [(vec others) e1])
                          e1)])])))))
      ;else
      `(let [a# ~(QMARK-expand env [b1 e1])]
         (if (success? a#)
           a# ~(QMARK-expand env more))))))

#?(:clj

   (do

     (defmacro ? [& body]
       (QMARK-expand {} body))

     (defmacro or
       ([] (failure ::empty-or))
       ([x] x)
       ([x & next]
        `(? [or# ~x] or# (or ~@next))))

     (defmacro and
       ([] true)
       ([x] x)
       ([x & next] `(? ~x (and ~@next))))

     (defmacro f [& xs]
       (let [{:keys [cases name]} (p/parse-fn xs)]
         `(fn ~name
            ~@(map (fn [[argv & body]]
                     (let [body (if (= 1 (count body)) (first body) (list* 'do body))
                           argv' (vec (take (count argv) (p/gensyms)))]
                       `(~argv' (? ~(vec (interleave argv argv')) ~body))))
                   cases))))

     (clojure.walk/macroexpand-all '(f iop ([x] x) ([(pos? x) [a b c]] (+ x a b c))))

     ()

     ((f iop ([x] x) ([(pos? x) [a b c]] (+ x a b c)))
      1)
     ))

(comment

  (g/get-spec! 'd/fail)

  (macroexpand '(g/implements? d/fail []))

  (require '[boot.prelude :as p :refer [is]])

  (g/get-spec! 'fail)
  (? (failure {:im :failing}) 1)
  (? (failure "iop") 1 (failure :catched))
  (? (failure {:im :failing}) 1 2)
  (let? [a (failure ::a)] a)
  (or (failure {:im :failing}) (failure :catched))

  (do :cs-tests

      (is 1 (? [a 1] a))

      (is failure0
          (? [a failure0] a))

      (is (failure "my failure")
          (? [a (failure "my failure")] a))

      (is 1 (? [a failure0] a 1))

      (is 1 (? [a failure0] a
               [b 1] b))

      (is (failure 2)
          (? [a failure0] a
             [b (failure 2)] b))

      (is :bottom
          (? [a (failure 1)
              _ (println "never")] a
             [something 42
              b (failure 2)] b
             :bottom))

      (d/bindings '!a failure0)

      (is [nil 1] (macroexpand '(? [?a failure0] [a 1] 2)))

      (is [0 1] (? [?a 0] [a 1] 2))

      (is ::catched
          (try (? [!a failure0] [a 1] 2) (catch Exception e ::catched)))

      (clojure.walk/macroexpand-all '(? [a failure0] a
                                        [b (failure 2)] b))

      (def recnt (atom 0))
      (macroexpand (QMARK-expand
                     {}
                     '([[a b c] failure0] a
                       [[a b c] (failure 2)] b
                       pouet)))

      (QMARK-expand
        {}
        '([[a b c] pouet] :iop :nop))

      (d/bindings '[a b c] 'xs)
      )

  )

(defn chain [fns]
  (if-not (seq fns)
    identity
    (fn [x]
      (loop [x x fns fns]
        (if-not fns
          x (? [x ((first fns) x)]
               (recur x (next fns))))))))

(defn fork [fns]
  (if-not (seq fns)
    (constantly failure)
    (fn [x]
      (loop [fns fns]
        (if (seq fns)
          (? [x ((first fns) x)]
             x (recur (next fns)))
          (failure `(fork ~@fns)))))))

;; predicate importation

;; predicate is a function that can return true or false
;; guard is a function that can return something or nil

(defn predicate->guard [f]
  (u/fn& [a] (when (f a ...) a)))

(defn wrap-guard [f fail]
  (u/fn& [a] (c/or (f a ...) (fail a ...))))

(defn wrap-predicate [f fail]
  (wrap-guard (predicate->guard f) fail))

(comment
  ;; brutal
  (def core-preds
    (keys (filter (fn [[s _]] (c/= \? (last (name s))))
                  (ns-map 'clojure.core))))

  )

(defn redloop [f a xs]
  (reduce (fn [a e] (or (f a e) (reduced failure)))
          a xs))

(def core-guards

  (reduce
    (fn [a s]
      (let [val (eval s)
            fail #(failure {:predicate s :args (vec %&)})
            g (wrap-predicate val fail)]
        (assoc a val g s g)))
    {}
    '[decimal?
      contains?
      every?
      qualified-keyword?
      satisfies?
      seq?
      fn?
      vector?
      any?
      isa?
      boolean?
      char?
      some?
      inst?
      simple-symbol?
      pos?
      sequential?
      neg?
      float?
      set?
      reversible?
      map?
      var?
      empty?
      string?
      uri?
      double?
      map-entry?
      int?
      associative?
      keyword?
      even?
      tagged-literal?
      indexed?
      counted?
      future?
      zero?
      simple-keyword?
      not-every?
      class?
      neg-int?
      sorted?
      nil?
      bytes?
      record?
      identical?
      ident?
      qualified-ident?
      true?
      integer?
      special-symbol?
      ratio?
      delay?
      ifn?
      nat-int?
      chunked-seq?
      distinct?
      pos-int?
      odd?
      uuid?
      false?
      list?
      simple-ident?
      rational?
      number?
      not-any?
      qualified-symbol?
      seqable?
      symbol?
      coll?

      = > >= < <=]))

#?(:clj (defmacro import-core-preds []
          `(do ~@(mapcat (fn [[s v]] `[(ns-unmap '~(p/ns-sym) '~s)
                                       (def ~s ~v)])
                         (filter (comp symbol? key) core-guards)))))



(? (seq? []) :a)




