(ns boot.core
  (:require [boot.generics :as g]
            [boot.types :as t]
            [boot.prelude :as p]
            [boot.state :as s]
            [matches.core :as m]
            [clojure.core :as c]))

(defmacro deft [name fields & body]
  `(do (m/deft ~name ~fields)
       (t/tag+ ~(keyword name) [(m/->class ~name)] [])
       (g/type+ ~(keyword name) ~@body)))

(p/import-macros
 tag+ t/tag+
 defg g/generic
 generic+ g/generic+
 defm m/defm)

(comment

  (defg greet
    ([x] "Yo!")
    ([x y] (str "Yo " y)))

  (g/generic yop [x])

  (deft num [val]
    (greet [x] "Hey!"))

  (greet (num 1))
  (greet "iop"))

