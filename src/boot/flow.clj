(ns boot.flow
  (:refer-clojure :exclude [> <])
  (:require [boot.prelude :as u :refer [f1 f_ defn+]]
            [boot.lenses :as l]))

;; links

(defn link [a b]
  (clojure.lang.MapEntry. a b))

(def link? map-entry?)

;; transformations

(defprotocol ITrans (->trans [x]))
(defprotocol ICombine (combine [x y]))

(defn trans? [x]
  (or (when (fn? x) x)
      (when (satisfies? ITrans x) (->trans x))))

(do :impl

    (declare trans step_)

    (defn vec->trans [v]
      (let [ts (map trans v)]
        (fn [y] (reduce #(%2 %1) y ts))))

    (defn link->trans [e]
      (fn [x]
        (l/mut x
               (key e)
               (step_ (val e)))))

    (defn map->trans [m]
      (vec->trans (mapv link->trans m))))

(defn trans
  "given anything, return a function representing a transformation (a reduction step of '> )
   used in 'step when its first argument (the seed) does not implement ICombine"
  [x]
  (or (trans? x)
      (cond
        (nil? x) identity
        (map? x) (map->trans x)
        (link? x) (link->trans x)
        (vector? x) (vec->trans x)
        :else (constantly x))))

;; flow

(defn+ step [x y]
  (if (satisfies? ICombine x)
    (combine x y)
    ((trans y) x)))

(defn+ >
       "thread x thru given transformations (xs) shortcircuiting on first nil result"
       [x & xs]
       (loop [x x xs xs]
         (if (and x xs)
           (recur (step x (first xs)) (next xs))
           x)))

(defn+ <
       "try all given transformations over x until the first non nil result"
       [x & xs]
       (loop [xs xs]
         (when (seq xs)
           (or (step x (first xs))
               (recur (next xs))))))

(defn at
  "arity 2:
    the at function returns a trans(able)
    built upon 'lenses/path, 'path does not have to point to an existing value to succeed
   variadic artity
    takes several couples (flat), that will be executed in order (by the transformation it returns)"
  ([path f]
   (link (l/path path) f))
  ([x y & zs]
   (reduce (fn [f [p g]]
             (comp (link->trans (at p g)) f))
           (link->trans (at x y))
           (partition 2 zs))))

(u/assert

 (= (> {:a {:b 1 :c -1}}
       {:a {:b inc :c dec}})
    (> {:a {:b 1 :c -1}}
       [{:a {:b inc}}
        {:a {:c dec}}])
    (> {:a {:b 1 :c -1}}
       {:a [{:b inc} {:c dec}]}))

  (> {:a {:b 1 :c -1}}
     {:a {:b inc}
      [:a :c neg?] dec})

  (= (> {}
        (at [:a :b :c] 42))
     (> {}
        {(l/path :a :b :c) 42}))

  (= (> {}
        (at [:a :b :c] 42 ;; this assoc 42 at path [:a :b :c]
            :d 'pouet
            [:e :f] '(1 2 3)
            [:a :b :c] inc ;; updates are executed sequentially so the previously assoced 42 value is available
            ))

     {:a {:b {:c 43}},
      :d 'pouet,
      :e {:f '(1 2 3)}}

     ;; when using map syntax, there is no garanty of order
     ;; here the equivalent of the previous form
     (> {}
        {(l/path [:a :b :c]) 42 ;; this assoc 42 at path [:a :b :c]
         (l/path :d) 'pouet
         (l/path [:e :f]) '(1 2 3)}
        ;; so our transformations, if depending on freshly assoced values, has to wait the next reduction step
        ;; in this case, since the value now exists, the key does not have to be wrapped in 'lenses/path
        {[:a :b :c] inc}))


  (let [t (<_ {pos? inc}
              {neg? dec}
              {l/id u/prob})]
    (and (= (t 1) 2)
         (= (t -1) -2)
         (= (t 0) 0)))

  (= ((>_ inc inc) 1)
     ((>_* [inc inc]) 1)
     ((>_* inc dec [inc inc]) 1)
     (>* 1 inc dec [inc inc])
     (> 1 (>_ inc inc)))

  (nil? (l/get 1 (l/! neg?)))

  (nil? (> 1 (link neg? inc)))

  (let [t (>_ {neg? inc}
              inc)]
    (and (= 1 (t -1))
         (nil? (t 1))))


  (nil? (> 1 (u/guard neg?) inc))

  (zero? (> -1 (u/guard neg?) inc))

  (= ((f_ (+ _ _)) 1)
     ((f1 x (+ x x)) 1)
     ((f1 {a :a} (+ a a)) {:a 1})))
