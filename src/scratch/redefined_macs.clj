(ns scratch.redefined-macs
  (:require [clojure.walk :as walk]
            [boot.prelude :as p]))

(def state (atom 0))

(defmacro yo [& xs]
  `(do (swap! state inc)
       (+ (p/prob @state) ~@xs)))

(defmacro mess []
  `(do (+ (yo 1 2) (yo 1 2))))

(macroexpand '(mess))

(mess)