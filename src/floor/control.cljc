(ns floor.control
  (:refer-clojure :exclude [or and])
  (:require [clojure.core :as c]
            [boot.generics :as g]
            [boot.named :as n]
            [boot.prelude :as p :refer [is]]
            [floor.declaration :as d :refer [failure]])
  #?(:cljs (:require-macros [boot.control :refer [? let? ?> ?<]])))

(def failure0 (failure ::failure))

(defn failure? [x] (g/implements? d/fail x))
(defn success? [x] (not (failure? x)))

(comment

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

      (is [nil 1] (? [?a failure0] [a 1] 2))

      (is [0 1] (? [?a 0] [a 1] 2))

      (is ::catched
          (try (? [!a failure0] [a 1] 2) (catch Exception e ::catched)))

      )

  )

#?(:clj

   (do (defmacro IF
         "you should not use this, please use `? instead"
         ([test then]
          `(let [t# ~test]
             (if (success? t#) ~then t#)))
         ([test then else]
          `(if (success? ~test) ~then ~else))
         ([test then test2 then2 & others]
          (IF ~test ~then (IF ~test2 ~then2 ~@others))))

       (defmacro ?
         ([] nil)
         ([return] return)
         ([bs then] `(? ~bs ~then nil))
         ([bs then else]
          (cond
            (not (vector? bs)) `(IF ~bs ~then ~@(when else [else]))
            (not (seq bs)) then
            :else
            (let [[pat expr & others] bs
                  [p1 e1 & bs] (d/bindings pat expr)]
              `(let ~[p1 e1]
                 (IF ~p1
                     (? ~(vec bs)
                        ~(if others
                           `(? ~(vec others) ~then ~else)
                           then))
                     ~@(when else [else]))))))
          ([b1 e1 b2 e2 & xs]
           `(? ~b1 ~e1 (? ~b2 ~e2 ~@xs))))

       (defmacro or
         ([] (failure ::empty-or))
         ([x] x)
         ([x & next]
          `(? [or# ~x] or# (or ~@next))))

       (defmacro and
         ([] true)
         ([x] x)
         ([x & next] `(IF ~x (and ~@next))))))

#_(clojure.walk/macroexpand-all '(let? [a 1 b 2] :io :no))
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

(defn pred->guard [f]
  (fn
    ([a] (if (f a) a failure))
    ([a b] (if (f a b) a failure))
    ([a b c] (if (f a b c) a failure))
    ([a b c d] (if (f a b c d) a failure))
    ([a b c d & others] (if (apply f a b c d others) a failure))))

(comment
  ;; brutal
  (def core-preds
    (keys (filter (fn [[s _]] (c/= \? (last (name s))))
                  (ns-map 'clojure.core))))

  #?(:clj (defmacro import-core-preds []
            `(do ~@(mapv (fn [[s v]] `(def ~s (pred->guard ~v)))
                         core-preds)))))

(defn redloop [f a xs]
  (reduce (fn [a e] (or (f a e) (reduced failure)))
          a xs))

(def core-guards

  (reduce
    (fn [a k]
      (assoc a k (pred->guard k)))
    {}
    [decimal?
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

