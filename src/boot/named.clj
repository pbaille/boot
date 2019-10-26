(ns boot.named
  (:refer-clojure :exclude [cat cons str])
  (:require [clojure.string :as s]
            [clojure.core :as c]))

;; casting --------------------------------------------------------

(defn nswap
  ([f]
   (partial nswap f))
  ([f x & args]
   (let [ret (apply f (name x) args)]
     (cond
       (string? x)  ret
       (symbol? x)  (symbol ret)
       (keyword? x) (keyword ret)))))

(defmacro nfn
  ([e]
   `(nfn [~'_] ~e))
  ([argv & body]
   `(nswap (fn ~argv ~@body))))

(defmacro defnf [n & form]
  `(def ~n (nfn ~@form)))

;; cases ----------------------------------------------------------
;; from funcool.cuerdas

(defn- stylize-split
  [s]
  (let [re1 (re-pattern "(\\p{Lu}+[\\p{Ll}\\u0027\\p{Ps}\\p{Pe}]*)")
        re2 (re-pattern "[^\\p{L}\\p{N}\\u0027\\p{Ps}\\p{Pe}]+")]
    (some-> s
            (name)
            (s/replace re1 "-$1")
            (s/split re2)
            (seq))))

(defn- stylize-join
  ([coll every-fn join-with]
   (when (seq coll)
     (s/join join-with (map every-fn coll))))
  ([[fst & rst] first-fn rest-fn join-with]
   (when (string? fst)
     (s/join join-with (c/cons (first-fn fst) (map rest-fn rst))))))

(defn stylize
  ([s every-fn join-with]
   (stylize s every-fn every-fn join-with))
  ([s first-fn rest-fn join-with]
   (let [remove-empty #(seq (remove empty? %))]
     (some-> (stylize-split s)
             (remove-empty)
             (stylize-join first-fn rest-fn join-with)))))

(def cap (nswap s/capitalize))
(def low (nswap s/lower-case))

(def snake  (nfn (stylize _ low "_")))
(def kebab  (nfn (stylize _ low "-")))
(def camel  (nfn (stylize _ low cap "")))
(def pascal (nfn (stylize _ cap "")))

;; common ops -----------------------------------------------------

(defnf pure [x] "")

(defnf cat [& xs]
  (apply c/str (map name xs)))

(defn split
  ([x]
   (map #(cat (pure x) (low %))
        (stylize-split x)))
  ([x re]
   (map #(cat (pure x) %)
        (s/split (name x) re))))

(defn builder [empty]
  (fn
    ([] empty)
    ([& xs] (apply cat empty xs))))

(def str (builder ""))
(def sym (builder (symbol "")))
(def kw  (builder (keyword "")))
