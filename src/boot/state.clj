(ns boot.state
  (:refer-clojure :exclude [reset! swap! get get-in])
  (:require [clojure.core :as c]))

(def state0
  {:clj
   {:fns {}
    :types {}
    :guards {}
    :namespaces {}}
   :cljs
   {:fns {}
    :types {}
    :guards {}
    :namespaces {}}})

(def state (atom state0))

(def debug (atom nil))

(def ^:dynamic *expansion-state*
  {:env nil :form nil})

(defn env [] (:env *expansion-state*))
(defn form [] (:form *expansion-state*))
(defn cljs? [] (boolean (:ns (env))))
(defn clj-state [] (:clj @state))
(defn cljs-state [] (:cljs @state))

(defn current []
  (if (cljs?) (cljs-state) (clj-state)))

(defn get
  ([] (current))
  ([k] (c/get (current) k)))

(defn get-in [p]
  (c/get-in (current) p))

(defn compilation-target []
  (if (cljs?) :cljs :clj))

(defmacro expanding [& body]
  `(binding [*expansion-state*
             {:env ~'&env :form ~'&form}]
     ~@body))

(defmacro targeting-cljs [& xs]
  `(binding [*expansion-state* {:env {:ns true}}]
     ~@xs))

(defn swap! [f & args]
  (c/swap! state update (compilation-target) #(apply f % args)))

(defn reset!
  ([] (reset! state0))
  ([x] (clojure.core/reset! state x)))