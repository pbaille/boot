(ns floor.compiler
  (:require [boot.prelude :as p]
            [floor.composite :as compo]))

(p/use!)

(declare expand)

(def mobject0
  {:expand (fn [this env form] ($ form (p expand env)))
   :parse (fn [this env form] form)})

(defn mobject
  ([x]
   (cp x
       fn? (mobject {:expand x})
       holymap? (merge mobject0 x)))
  ([parse expand & more]
   (merge {:expand expand :parse parse} more)))

(defmacro expander [bindings & body]
  `(mobject {:expand (fn ~bindings ~@body)}))

(defn env-shadow [e x]
  (if (sequential? x)
    (reduce env-shadow e x)
    (let [{:keys [ns name]} (parse-symbol x)]
      (assoc-in e [ns name] mobject0))))

(defn env-get [e sym]
  (cs
    [{:keys [ns name]} (parse-symbol sym)
     found (get-in e [ns name])]
    (merge mobject0 found)
    ;; is symbol try to find metas
    (or (and (symbol? sym)
             (some-> sym resolve meta mobject))
        ;; else return the identity mobj
        mobject0)
    ))

(defn expand-seq
  [env form]
  (let [{:as mobj :keys [expand parse]}
        (env-get env (first form))]
    (expand mobj env (parse mobj env form))))

(defn expand [e x]
  (compo/expand
    (cp x
        seq? (expand-seq e x)
        holycoll? ($ x (p expand e))
        x)))

(defmacro def+ [name val metas]
  `(alter-meta!
     (def ~name ~val)
     (fn [m#] (merge m# ~metas))))

(def+ mvar (fn [x y z] z)
      {:expand (fn [_ _ _] :pouet)})

(do :assertions

    (is (expand {'floor.compiler {'rev (expander [_this env form] (reverse ($ (rest form) (p expand env))))}}
                '(rev 1 (mvar 2 4) [3 . xs] +)
                )
        '(+ (clojure.core/vec (clojure.core/concat [3] xs)) :pouet 1)))


