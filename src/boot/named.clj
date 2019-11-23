(ns boot.named
  (:refer-clojure :exclude [cat str])
  (:require [clojure.string :as s]
            [clojure.core :as c]
            [clojure.string :as str]))

;; casting --------------------------------------------------------

(defn named? [x]
  (or (string? x)(symbol? x)(keyword? x)))

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
    (println "a"(some-> s
                     (name)
                     (s/replace re1 "-$1")))
    (println "b"(some-> s
                     (name)
                     (s/replace re1 "-$1")
                     (s/split re2)))
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

(defn- name-seq [x]
  (cond (char? x) [(c/str x)]
        (named? x) [(name x)]
        (sequential? x) (mapcat name-seq x)))

(defnf cat
  [x & xs]
  (apply c/str (name-seq (cons x xs))))

(defn split
  ([x]
   (map #(cat (pure x) (low %))
        (stylize-split x)))
  ([x re]
   (map #(cat (pure x) %)
        (s/split (name x) re))))

(defn builder [empty & [sep]]
  (fn
    ([] empty)
    ([& xs]
     (if sep
       (cat empty (str/join sep (name-seq xs)))
       (cat empty xs)))))

(defnf join [sep x]
  (str/join sep (name-seq x)))

(def str0 "")
(def sym0 (symbol str0))
(def kw0 (keyword str0))

(def str (builder str0))
(def sym (builder sym0))
(def kw (builder key0))

(def dotstr (builder str0 "."))
(def dotsym (builder sym0 "."))
(def dotkey (builder kw0 "."))

