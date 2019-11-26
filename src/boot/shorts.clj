(ns boot.shorts
  (:refer-clojure :exclude [take drop cat defn fn])
  (:require [clojure.core :as c]
            [boot.prelude :as p :refer [defmac]]
            [boot.named :as n]))

;; short-circuiting application
;; in this model when a function receive a nil argument it returns nil

;; in addition we can make predicates return their first argument in case of success or nil otherwise
;; we will call this 'guards'
;; ex: (pos? x) returns x only if x is positive else returns nil
;; in conjunction of our previously described shortcircuiting model it let us write:
;; (+ (pos? x) y)
;; that will succeed only if x is positive and y is non nil

;; in order to ease composition and favor higher order function usage
;; we will change argument order of some core function,
;; prefering to place the manipulated object as first argument
;; e.g (take n '(a b c)) will become (take '(a b c) n)

;; with this in mind we can introduce a useful convention
;; (take_ 3) <=> #(take % 3)
;; function postfixed with _ are creating an arity 1 function that wait for an object to execute the computation
;; we will introduce facilities to derive _ variant from a regular function ('derive-obj-fn)

;; with those three ideas we hope to enhance basic clojure expressivity

;; function constructors ----------------------------------------------

(c/defn wrap-fn
  "turn a regular function into a shotcuicuited one"
  [f]
  (c/fn [& xs]
    (when (every? (complement nil?) xs)
      (apply f xs))))

(def wrap-pred
  (comp p/fn->guard wrap-fn))

(do

  :importing-utils

  (c/defn unqualify [s]
    (symbol (name s)))

  (c/defn import-fn [s]
    `(def ~(unqualify s) (wrap-fn ~s)))

  (c/defn import-pred [s]
    `(def ~(unqualify s) (wrap-pred ~s)))

  (c/defn qualify-syms [ns xs]
    (map #(n/sym ns "/" %) xs))

  (defmac import-core-fns [& xs]
    `(do (doseq [s# '~(vec xs)] (ns-unmap *ns* s#))
         ~@(map import-fn (qualify-syms 'clojure.core xs))))

  (defmac import-core-preds [& xs]
    `(do (doseq [s# '~(vec xs)] (ns-unmap *ns* s#))
         ~@(map import-pred (qualify-syms 'clojure.core xs)))))

(defmac fn [& bod]
  `(wrap-fn (c/fn ~@bod)))

(defmac defn [n & bod]
  `(def ~n (fn ~@bod)))

(import-core-fns
  + - * /
  inc dec
  cons apply
  reverse nth)

(import-core-preds
  pos? neg?
  > < >= <= =
  vector? seq? map? set? fn?
  number? symbol? keyword? string?)

(defn cat [x & xs] (p/cat* x xs))
(defn take [x n] (c/take n x))
(defn drop [x n] (c/drop n x))
(defn apnd [x & xs] (concat x xs))
(defn snoc [x & xs] (reduce (p/flip cons) x xs))

(do :demo

 ;; data
 (def r1 (range 10))
 (def n nil)
 (def m 2)

 ;; exemples
 (+ n 2)
 (+ n m)                                ;nil

 (take r1 m)
 (take r1 n) ;; nil
 (cat r1 r1)
 (cat r1 (take r1 m))
 (cat r1 (take r1 (+ m n))) ;; nil

 (snoc () 1 2 3 4)

 ;; defns
 (defn f1 [x y]
   (or (snoc (vector? x) y) ;; if (vector? x) succeed it returns x, so (if y is not nil) the snoc form succeed
       (apnd (seq? x) y)))  ;; else it tries the second form

 (f1 [1 2 3] 4)
 (f1 '(1 2 3) 4)

 (defn nth' [x n]
   (or
    (nth x (>= n 0)) ;; same here (>= n 0) returns n or nil shortcircuiting or not the nth form
    (nth (reverse x) (- (neg? n)))))

 (nth' r1 2)
 (nth' r1 -2)
 (nth' r1 0)
 (nth' nil 42)
 (nth' r1 nil)

 ;; function with an or expr as body seems recurent in this model
 ;; lets create a macro for this

 (defmac nod [fb & rb]
   (let [[name [argv & cases]]
         (if (symbol? fb) [fb rb] [(gensym) (cons fb rb)])]
     `(fn ~name ~argv (c/or ~@cases))))

 (defmac defnod [name & bod]
   `(def ~name (nod ~@bod)))

 (defnod nth'' [x n]
   (nth x (>= n 0))
   (nth (reverse x) (- (neg? n))))

 (nth'' r1 2)
 (nth'' r1 -2)
 (nth'' r1 0))

;; object fn derivation ------------------------------------

(c/defn obj-fn
  [f]
  (fn [& xs]
    (fn [x] (apply f x xs))))

(c/defn derive-obj-fn [f]
  `(def ~(symbol (str f "_")) (obj-fn ~f)))

(defmac derive-obj-fns [& xs]
  `(do ~@(map derive-obj-fn xs)))

(derive-obj-fns cat snoc apnd take drop > < >= <= =)


