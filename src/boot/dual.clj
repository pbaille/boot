(ns boot.dual
  (:require [boot.prelude :as p]
            [matches.core :refer [deft]]))

(p/use!)

;; experimental WIP
;; the initial intent here is to become able to define functions that have compile time preprocessing
;; this has been done many times, last iteration is in asparagus

(deft mfn [expand call])

(defn expandable? [x]
  (and (seq? x)
       (some-> x first mfn?)))

(defn expand

  [x]
  #_(pp 'expand x)
  (cp x
      ;; macro call
      expandable?
      (apply (-> x first :expand)
             (rest x))
      ;; clojure collection
      holycoll? ($ x expand)
      ;; anything else
      x))

(defmacro m-resolve [x]
  (println &env)
  (resolve &env x))

(let [map 42]
  (m-resolve filter))


