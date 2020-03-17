(ns floor.vars
  (:refer-clojure :exclude [resolve])
  (:require [clojure.core :as c]
            [boot.prelude :as p :refer [cs cp is]]
            [clojure.string :as str]
            [boot.named :as n]))

(def SEPARATOR "_")

(defn mksym [& xs]
  (let [parts (remove nil? (flatten xs))]
    (when (seq parts)
      (n/sym (interpose SEPARATOR parts)))))

(defn splitsym [sym]
  (when sym
    (str/split (name sym) (re-pattern SEPARATOR))))

(defn qualified-sym [ns & xs]
  (symbol (name (or ns (p/ns-sym)))
          (n/str xs)))

(defn resolve-sym

  ([sym]
   (cs [v (c/resolve sym)]
       (p/var-symbol v)))

  ([sym from]
   (cs [ns-str (and from (namespace from))
        fullsym (mksym from sym)]
       (resolve-sym (qualified-sym ns-str fullsym))
       from
       (resolve-sym sym (mksym (butlast (splitsym from))))
       (resolve-sym sym)))

  ([sym from {:keys [shadows aliases]}]
   (cs [ns (namespace sym)]
       (cs [v (get-in aliases [from (symbol ns)])]
           (or (resolve-sym (mksym v (name sym)))
               (resolve-sym (qualified-sym v (name sym))))
           (resolve-sym sym from))

       ((set shadows) sym) nil

       (resolve-sym sym from))))

(defn resolve
  [x from options]
  (cp x
      symbol? (or (resolve-sym x from options) x)
      p/holycoll? (p/$ x #(resolve % from options))
      x))

(defmacro in [at & xs]
  (let [[aliases & body] (if (map? (first xs)) xs (cons nil xs))]
    (resolve (list* 'do body) at {:aliases aliases})))

(do :assertions

    (def foo_bar_baz 1)
    (def foo_bob 2)
    (def pouet 3)

    (is 'floor.vars/pouet
        (resolve-sym 'pouet 'foo_bar))
    (is 'floor.vars/foo_bob
        (resolve-sym 'bob 'foo_bar)
        (resolve-sym 'bob 'foo_bar {}))

    (def options
      '{:aliases {iop {fb foo_bar s clojure.string}}
        :shadows #{}})

    (is 'floor.vars/foo_bar_baz
        (resolve-sym 'fb/baz 'iop options)
        (resolve-sym 'bar_baz 'foo options)
        (resolve-sym 'bar_baz 'foo_bar options))
    (is 'clojure.string/split
        (resolve-sym 's/split 'iop options))

    (resolve-sym 'println nil nil)
    (macroexpand '(in foo_bar
         (println baz))))



