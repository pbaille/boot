(ns floor.compiler.env
  (:require [floor.compiler.composite :as compo]
            [boot.prelude :as p :refer [cp cs $ p is]]))

(do :env

    (declare expand)

    (def mobject0
      {:expand (fn [env form] ($ form (p expand env)))
       :parse (fn [env form] form)})

    (defn mobject
      ([x]
       (cp x
           fn? (mobject {:expand x})
           p/holymap? (merge mobject0 x)))
      ([parse expand & more]
       (merge {:expand expand :parse parse} more)))

    (defmacro expander [bindings & body]
      `(mobject {:expand (fn ~bindings ~@body)}))

    (defn env-shadow [e x]
      (if (sequential? x)
        (reduce env-shadow e x)
        (let [{:keys [ns name]} (p/parse-symbol x)]
          (assoc-in e [ns name] mobject0))))

    (defn env-get [e sym]
      (cs
        [{:keys [ns name]} (p/parse-symbol sym)
         found (get-in e [ns name])]
        (merge mobject0 found)
        ;; is symbol try to find metas
        #_(when (symbol? sym)
          (some-> sym resolve meta mobject)))))

(do :expand

    (defn expand-seq
      [env form]
      (if-let [mobj (env-get env (first form))]
        ((:expand mobj) env ((:parse mobj) env form))
        ($ form (p expand env))))

    (defn expand-sym
      [env sym]
      (let [{:keys [substitute]}
            (env-get env sym)]
        (if substitute
          (expand env substitute)
          sym)))

    (defn expand [env form]
      (compo/expand
        (cp form
            p/unquote? (eval (expand env (second form)))
            seq? (expand-seq env form)
            p/holycoll? ($ form (p expand env))
            symbol? (expand-sym env form)
            form)))

    (defmacro def+ [name val metas]
      `(alter-meta!
         (def ~name ~val)
         (fn [m#] (merge m# ~metas))))

    (def+ mvar (fn [y z] z)
          {:expand (fn [_ _] :pouet)})

    #_(do :assertions

        (expand {} `(= 1 2))

        (env-get {} '=)

        (is (expand {'floor.compiler.env {'rev (expander [env form] (reverse ($ (next form) (p expand env))))}}
                    '(rev 1 (mvar 2 4) [3 . xs] +)
                    )
            '(+ (clojure.core/vec (clojure.core/concat [3] xs)) :pouet 1))))