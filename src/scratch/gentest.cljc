(ns scratch.gentest
  (:require [boot.generics :as g :refer-macros [generic generic+ cljs?]]))

(comment
  (generic g1 [x]
           ;; prim type impl
           :vec :g1vec
           ;; this type is a group
           ;; under the hood it implements for all collections
           :coll [:g1coll x]
           ;; group litteral can be handy
           #{:key :sym} :key-or-sym)

  (generic+ g1 [x]
            ;; str impl
            :str [:str x]
            ;; if a last expresion is given it extends Object
            [:unknown x]))


