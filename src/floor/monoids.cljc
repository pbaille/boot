(ns floor.monoids
  (:refer-clojure :exclude [+ vals iter vec map set str key])
  (:require [clojure.core :as c]
            [floor.utils :as u]
            [floor.declaration :as d]
            [boot.prelude :as p]
            [boot.generics :as g]))

(g/generic+
  d/pure
  [_]
  :fun identity
  :vec []
  :lst ()
  :map {}
  :set #{}
  :str ""
  :sym (symbol "")
  :key (keyword "")
  #{:nil :any} nil)

(g/generic+
  d/pure?
  [x]
  :lst (when-not (seq x) ())
  (when (= x (d/pure x)) x))

(g/generic+
  d/sip [a b]
  :lst (concat a [b])
  #{:set :vec} (conj a b)
  :map (assoc a (first b) (second b))
  :fun (partial a b)
  :nil (list b))

(g/generic+
  d/+
  [a b]
  :fun (comp b a)
  :lst (concat a (d/iter b))
  :str (c/str a b #_(.toString b))
  :sym (symbol (c/str (name a) b #_(.toString b)))
  :key (keyword (c/str (name a) (name b)))
  :num (c/+ a b)
  :nil (d/iter b)
  :any (reduce sip a (d/iter b)))

(def wrap (u/fn& [x] (d/sip (d/pure x) ...)))
(def wrap+ (u/fn& [x] (d/+ (d/pure x) ...)))
(def wrap* (partial apply wrap))
(def wrap+* (partial apply wrap+))

(defmacro defwrapped
  ([[n e]]
   (let [n+ (p/sym n "+")
         n* (p/sym n "*")
         n+* (p/sym n "+*")]
     `(do
        (def ~n (u/fn& [] (d/sip ~e ...)))
        (def ~n+ (u/fn& [] (d/+ ~e ...)))
        (def ~n* (u/fn& [x#] (apply ~n x# ...)))
        (def ~n+* (u/fn& [x#] (apply ~n+ x# ...))))))
  ([x & xs]
   `(do ~@(c/map #(list `defwrapped %) (cons x xs)))))

(defwrapped
  [lst ()]
  [vec []]
  [set #{}]
  [map {}])

(def str
  c/str)

(def str*
  (u/fn& [x] (apply c/str x ...)))
(def key
  (u/fn& [] (d/+ (c/keyword "") ...)))
(def key*
  (u/fn& [x] (apply key x ...)))
(def sym
  (u/fn& [x] (d/+ (c/symbol (c/name x)) ...)))
(def sym*
  (u/fn& [x] (apply sym x ...)))

