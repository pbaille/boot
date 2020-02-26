(ns boot.state
  (:refer-clojure :exclude [reset!]))

(def state0
  {:fns {}
   :types {}
   :guards {}
   :namespaces {}})

(def state (atom state0))

(def ^:dynamic *cljs?* nil)
(def ^:dynamic *expansion-env* nil)

(defmacro binding-expansion-dynamic-vars [& body]
  `(binding [*expansion-env* (or *expansion-env* ~'&env)
             *cljs?* (or *cljs?* (boolean (:ns ~'&env)))]
     ~@body))

(defmacro if-cljs [then else]
  `(if *cljs?* ~then ~else))

#_(defn qualify-symbol [x]
  (when (symbol? x)
    (if-cljs
      (:name (cljs.analyzer/resolve-var *expansion-env* x))
      (if-let [v (resolve *expansion-env* x)]
        (let [{:keys [ns name]} (meta v)]
          (symbol (str ns) (str name)))))))

(defn target-kw []
  (if-cljs :cljs :clj))

(defn reset! []
  (clojure.core/reset! state state0))