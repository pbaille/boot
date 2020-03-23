(ns floor.compiler.composite
  (:require [boot.prelude :as p :refer [cp is]]))

(def dot '.)
(def dotdot '..)
(defn dot? [x] (= dot x))
(defn dotdot? [x] (= dotdot x))

(defn- dot-split
  "split a collection at first encountered dot,
  keeping it as the head of the second part"
  [c]
  (split-with (complement '#{. ..}) c))

(def dotted?
  (fn [x]
    (cp x
        map? (contains? x dot)
        sequential? (p/indexof x dot)
        nil)))

(defn composed?
  "x contains some composition operators
   (. and/or ..)"
  [x]
  (cp x
      p/quote? nil
      map? (or (contains? x dot) (contains? x dotdot))
      sequential? (or (p/indexof x dot) (p/indexof x dotdot))
      nil))

(defn not-composed? [x]
  (not (composed? x)))

(defn single-dotted?
  "x has only one dot (useful in bind)"
  [x]
  (and (dotted? x)
       (cp x
           map? (not (contains? x dotdot))
           sequential?
           (and (not (p/indexof x dotdot))
                (= 1 (count (filter dot? x)))))))


(defn seq-parts [s]
  (loop [[fs ss & rs] s ret []]
    (cp fs
        not ret
        dot? (recur rs (conj ret ss))
        dotdot? (p/catv (conj ret ss) rs)
        (recur (cons ss (or rs ()))
               (if (vector? (last ret))
                 (conj (vec (butlast ret)) (conj (last ret) fs))
                 (conj ret [fs]))))))

(declare expand)

(defn expand-map [x]
  (let [dotpart (get x dot)]
    (list* `merge
           (expand (dissoc x dot))
           (if (vector? dotpart)
             (map expand dotpart)
             [(expand dotpart)]))))

(defn expand-seq [x]
  (if (dot? (first x))
    `(p/call* (concat ~@(map expand (seq-parts x))))
    (let [[heads tail] (dot-split x)
          tail (if-not (next (next tail))
                 (second tail)
                 `(concat ~@(map expand (seq-parts tail))))]
      `(apply ~@heads ~tail))))



(defn expand-vec [x]
  `(vec (concat ~@(map expand (seq-parts x)))))

(defn expand [x]
  (cp x

      composed?
      (cp x
          vector? (expand-vec x)
          seq? (expand-seq x)
          map? (expand-map x))

      p/holycoll?
      (p/$ x expand)

      x))

(do :assertions

    ;; vecs --------

    (is (expand '[a b . c])
        '(clojure.core/vec (clojure.core/concat [a b] c)))

    (is (expand '[a b . c . d])
        '(clojure.core/vec (clojure.core/concat [a b] c d)))

    (is (expand '[a b .. c d])
        '(clojure.core/vec (clojure.core/concat [a b] c d)))

    ;; maps --------

    (is (expand '{:a 1 . b})
        '(clojure.core/merge {:a 1} b))

    (is (expand '{:a 1 . [b c d]})
        '(clojure.core/merge {:a 1} b c d))

    ;; lists -------

    (is (expand '(fun a b . c))
        '(clojure.core/apply fun a b c))

    (is (expand '(fun a . b c))
        '(clojure.core/apply fun a (clojure.core/concat b [c])))

    (is (expand '(fun a b . c . d))
        '(clojure.core/apply fun a b (clojure.core/concat c d)))

    (is (expand '(fun a b .. c d e))
        '(clojure.core/apply fun a b (clojure.core/concat c d e)))

    )

