(ns scratch.nsub-expand
  (:require [clojure.string :as str]))

(defonce state (atom {}))

(def NSUB_POSTFIX "_NS")

(defn parent-seq
  ([nsym] (parent-seq @state nsym))
  ([nss nsym] (parent-seq nss nsym ()))
  ([nss nsym ret]
   (when-let [p (get-in nss [nsym :parent])]
     (concat (parent-seq nss p)
             (cons p ret)))))

(defn fullname [x]
  (if (string? x) x
                  (if-let [ns (namespace x)]
                    (str ns "/" (name x))
                    (name x))))

(defn sym [& xs]
  (->> xs
       (remove nil?)
       (map fullname)
       (apply str)
       symbol))

(defn ns-sym [] (symbol (str *ns*)))

(defn nsub-parse [[name & body]]
  {:name name
   :body body
   :ns (ns-sym)
   :ctx []})

(defn dotsym [& xs]
  (apply sym (interpose "." (flatten xs))))

(defn nsub-form? [x]
  (and (seq? x) (= 'nsub (first x))))

(defn nsub-fn

  ;; expander
  [{:keys [name body ctx ns]}]
  (let [fullname (dotsym ns ctx (sym name NSUB_POSTFIX))
        ns-sym (dotsym ns ctx)
        [ns-body decls] (split-with (comp keyword? first) body)
        ;required (vec (remove '#{self} (get-in @st/state [:namespaces :locals ns-sym] [])))
        ]

    (swap! state
           #(-> %
                (assoc-in [ fullname :childs] #{})
                (assoc-in [ fullname :parent] ns-sym)
                (update-in [ ns-sym :childs] (fnil conj #{}) (sym name NSUB_POSTFIX))))

    `(do (~'ns ~fullname ~@ns-body)
         #_(~'require '[~ns-sym :refer :all #_~required])
         ~@(mapv (fn [n] `(~'require '[~n :refer :all #_~required])) (parent-seq fullname))
         (~'ns-unmap '~fullname '~'self)
         (~'declare ~'self)
         ~@(mapv (fn [e]
                   (if (nsub-form? e)
                     (nsub-fn (update (nsub-parse (next e))
                                      :ctx conj (sym name NSUB_POSTFIX)))
                     e))
                 decls)
         (~'ns ~ns-sym)
         (~'require '[~fullname :as ~name])
         ~@(for [n (range (count ctx))]
             (let [ns-sym (dotsym ns (take n ctx))
                   alias-sym (dotsym (map #(str/replace % NSUB_POSTFIX "") (drop n ctx)) name)]
               `(do
                  (~'ns ~ns-sym)
                  (~'require '[~fullname :as ~alias-sym]))))
         (~'ns ~ns-sym)
         (def ~name ~(sym name "/self"))
         ))
)

(defn do-block? [x] (and (seq? x) (= 'do (first x))))

(defn remove-top-level-do-blocks [x]
  (if (do-block? x)
    (mapcat remove-top-level-do-blocks (next x))
    [x]))

(defn nsub-expand [body]
  (-> body nsub-parse nsub-fn
      remove-top-level-do-blocks
      vec ))

(nsub-expand '(aze
                    (:require [boot.fn :as fn])
                    (fn/defn add [x y] (+ x y))
                    (defn self [& _] "i'm the aze sub module")
                    (nsub bop
                          (defn self [& _] "i'm the bop sub module")
                          (def loula 33))
                    (nsub lou
                          (def self "value module"))))