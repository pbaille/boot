(ns boot.control
  (:refer-clojure :exclude [or and])
  (:require [clojure.core :as c])
  #?(:cljs (:require-macros [boot.control :refer [? let? ?> ?<]])))

(def failure ::failure) ;; try to replace this with nil and check perf gain
;; it could also be a dynamic var
(defn failure? [x] (= x failure))
(defn success? [x] (not= failure x))

#?(:clj

   (do (defmacro ? [test then & [else]]
         `(if (success? ~test) ~then ~(c/or else failure)))

       (defmacro let? [[pat expr & others] then & [else]]
         `(let [x# ~expr]
            (if (success? x#)
              (let [~pat x#] ~(if others `(let? ~(vec others) ~then ~else) then))
              ~(c/or else failure))))

       (defmacro or
         ([] failure)
         ([x & next] `(let? [or# ~x] or# (or ~@next))))

       (defmacro and
         ([] true)
         ([x] x)
         ([x & next] `(? ~x (and ~@next))))))

#_(clojure.walk/macroexpand-all '(let? [a 1 b 2] :io :no))
(defn chain [fns]
  (if-not (seq fns)
    identity
    (fn [x]
      (loop [x x fns fns]
        (if-not fns
          x (let? [x ((first fns) x)]
                  (recur x (next fns))))))))

(defn fork [fns]
  (if-not (seq fns)
    (constantly failure)
    (fn [x]
      (loop [fns fns]
        (if (seq fns)
          (let? [x ((first fns) x)]
                x (recur (next fns)))
          failure)))))

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

