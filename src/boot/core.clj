(ns boot.core
  (:require [boot.generics :as g]
            [boot.types :as t]
            [boot.prelude :as p]
            [boot.state :as s]
            [clojure.core :as c]))

(p/import-macros
 tag+ g/tag+
 defg g/generic
 generic+ g/generic+
 isa t/isa)



