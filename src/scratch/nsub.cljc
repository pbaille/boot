(ns scratch.nsub
  (:require
    [clojure.core :as c]
    [clojure.string :as str]
    [boot.prelude :as p :refer [use!]]
    [boot.named :as n]
    [boot.fn :as fn]
    [boot.state :as st]
    [boot.prelude :as u])
  #?(:cljs (:require-macros [boot.prelude :refer [use!]]
                            [scratch.nsub :refer [nsub]])))

(use!)

;; the intent here is to provide a mecanism that permits the definition of subnamespaces
;; In clojure, the common practice is to define one namespace per file, along with an isomorphic (I use fancy words) folder structure.
;; It's annoying me sometimes so I've done this

(defn find-defs
  "simplistic way to find nsub first level inner defs"
  [forms]
  #_(println 'find-defs forms)
  (vec (flatten
         (keep
           (fn [x]
             (or (and (seq? x)
                      (or (and
                            (re-matches #"^def.*" (name (first x)))
                            (second x))
                          (and (= 'do (first x))
                               (find-defs (next x)))))
                 nil))
           forms))))

(find-defs '(do (fn/defn add [x y] (+ x y))
                (defn self [& _] "i'm the aze sub module")
                (do (def pouet 1) (do (defn opo [x] x) (def ert 6)))
                (nsub bop
                      (defn self [& _] "i'm the bop sub module")
                      (def loula 33))
                (nsub lou
                      (def self "value module"))))

(def NSUB_POSTFIX "_NS")

(defn parent-seq
  ([nsym] (parent-seq (:namespaces @st/state) nsym))
  ([nss nsym] (parent-seq nss nsym ()))
  ([nss nsym ret]
   (when-let [p (get-in nss [nsym :parent])]
     (concat (parent-seq nss p)
             (cons p ret)))))

(:namespaces @st/state)
(swap! st/state update :namespaces (constantly nil))

(parent-seq 'boot.nsub.aze_NS.lou_NS)

#?(:clj
   (defmac+ nsub

            ;; expander
            [name body ctx ns]
            (let [fullname (n/dotsym ns ctx (sym name NSUB_POSTFIX))
                  ns-sym (n/dotsym ns ctx)
                  [ns-body decls] (split-with (comp keyword? first) body)
                  ;required (vec (remove '#{self} (get-in @st/state [:namespaces :locals ns-sym] [])))
                  ]

              (swap! st/state
                     #(-> %
                          (assoc-in [:namespaces fullname :locals] (find-defs decls))
                          (assoc-in [:namespaces fullname :childs] #{})
                          (assoc-in [:namespaces fullname :parent] ns-sym)
                          (update-in [:namespaces ns-sym :childs] (fnil conj #{}) (sym name NSUB_POSTFIX))))

              (u/pprob `(do (~'ns ~fullname ~@ns-body)
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
                                (let [ns-sym (n/dotsym ns (take n ctx))
                                      alias-sym (n/dotsym (map #(str/replace % NSUB_POSTFIX "") (drop n ctx)) name)]
                                  `(do
                                     (~'ns ~ns-sym)
                                     (~'require '[~fullname :as ~alias-sym]))))
                            (~'ns ~ns-sym)
                            (def ~name ~(sym name "/self"))
                            )))

            ;; parser
            [name & body]
            {:name name
             :body body
             :ns (ns-sym)
             :ctx []}))

(do
  (macroexpand '(nsub aze
                      (:require [boot.fn :as fn])
                      (fn/defn add [x y] (+ x y))
                      (defn self [& _] "i'm the aze sub module")
                      (nsub bop
                            (defn self [& _] "i'm the bop sub module")
                            (def loula 33))
                      (nsub lou
                            (def self "value module"))))

  (def pouetpouet 1)
  (nsub aze ;; creates a subnamespace aze
        (:require [boot.fn :as fn])
        (fn/defn add [x y] (+ pouetpouet x y))
        (defn self [& _] "i'm the aze sub module")
        ;; creates a sub sub ns bop that have access to all the content of its parent
        (nsub bop
              (defn self [& _] "i'm the bop sub module")
              (def loula 33))
        (nsub lou
              (def self "value module")
              (defn louadd [x y] (add x y))))

  (p/assert
    (= 35 (aze/add 1 aze.bop/loula) (aze.lou/louadd 1 aze.bop/loula))
    (= "i'm the bop sub module" (aze/bop))
    (= "value module" aze/lou)))

#_(do (ns my.ns
      (:require [clojure.string :as s]))
    (s/split "a.b.c" "."))




#_(:clj (do :nsub

            (defmac+ nsub

                     ;; expander
                     [name body ctx ns]
                     (let [fullname (n/dotsym ns ctx name)
                           ns-sym (n/dotsym ns ctx)
                           [ns-body decls] (split-with (comp keyword? first) body)]

                       ;; we have to keep track of subnamespaces in order to be able to know to which toplevel namespace they belong
                       ;; this way, when we will patch core/ns, we will be able to require recursively subnamespaces along with the required namespace
                       (swap! st/state
                              #(-> %
                                   (assoc-in [:namespaces fullname] #{})
                                   (update-in [:namespaces ns-sym] (fnil conj #{}) name)))

                       `(do (ns ~fullname ~@ns-body)
                            (~'use '~ns-sym)
                            #_(~'use '[~ns-sym :exclude [~'self]])
                            #_(~'use ['~ns-sym :exclude ['~'self]])
                            (~'ns-unmap '~fullname '~'self)
                            (declare ~'self)
                            ~@(mapv (fn [e]
                                      (if (nsub-form? e)
                                        (nsub-fn (update (nsub-parse (next e))
                                                         :ctx conj name))
                                        e))
                                    decls)
                            (in-ns '~ns-sym)
                            (require '[~fullname :as ~name])
                            #_(require ['~fullname :as '~name])
                            ~@(for [n (range (count ctx))]
                                (let [ns-sym (n/dotsym ns (take n ctx))
                                      alias-sym (n/dotsym (drop n ctx) name)]
                                  `(do
                                     (in-ns '~ns-sym)
                                     (require '[~fullname :as ~alias-sym])
                                     #_(require ['~fullname :as '~alias-sym]))))
                            (in-ns '~ns-sym)
                            (def ~name ~(sym name "/self"))))

                     ;; parser
                     [name & body]
                     {:name name
                      :body body
                      :ns (ns-sym)
                      :ctx []})

            #?(:cljs (filter (fn [z] z) (range 10)))

            (comment :tests

                     (nsub aze
                           (:require [boot.fn :as fn])
                           (fn/defn add [x y] (+ x y))
                           (defn self [& _] "i'm the aze sub module")
                           (nsub bop
                                 (defn self [& _] "i'm the bop sub module")
                                 (def loula 33))
                           (nsub lou
                                 (def self "value module")))

                     (macroexpand '(nsub aze
                                         (:require [boot.fn :as fn])
                                         (fn/defn add [x y] (+ x y))
                                         (defn self [& _] "i'm the aze sub module")
                                         (nsub bop
                                               (defn self [& _] "i'm the bop sub module")
                                               (def loula 33))
                                         (nsub lou
                                               (def self "value module"))))

                     (swap! st/state dissoc :namespaces)

                     (:namespaces @st/state)

                     (assert
                       (= 33 aze.bop/loula)
                       (aze/bop)
                       (= "value module" aze/lou)))))

;; The annoying thing with this is that if you require this namespace from elsewhere, only the top level namespace will be required
;; so I had to patch core/ns to behave in a way that requiring a namespace containing sub namespaces also requires subnamespaces aliased with the correct prefix

(comment :clj-xperiments
         #_(_ :ns

              (defn sub-namespaces_aux [ns-sym]
                (let [subs (get-in @st/state [:namespaces ns-sym])]
                  (if subs
                    (cons ns-sym (mapcat #(sub-namespaces_aux (n/dotsym ns-sym %)) subs))
                    (list ns-sym))))

              (defn sub-namespaces [s]
                (next (map #(n/sym (str/replace (c/name %) (n/str s ".") ""))
                           (sub-namespaces_aux s))))

              (defn require+ [xs]
                (let [xs
                      (reduce
                        (fn [a e]
                          (merge
                            a (if (vec? e)
                                {(first e) (merge {:as (first e)
                                                   :form e}
                                                  (apply hash-map (next e)))}
                                {e {:form [e :as e]
                                    :as e}})))
                        {} xs)
                      compile-element
                      (fn [[name {:keys [as form]}]]
                        (cons form
                              (for [sub (prob (sub-namespaces name))]
                                [(n/dotsym name sub) :as (n/dotsym as sub)])))]
                  (cons :require
                        (mapcat
                          compile-element
                          xs))))

              ;; we keep a copy of the core/ns initial implementation
              (defonce ns-impl @#'ns)

              ;; we wrap it with our custom require
              (alter-var-root
                #'clojure.core/ns
                (fn [_]
                  (fn [a b & xs]
                    ;; (println "expanding ns" xs)
                    (apply ns-impl a b
                           (map (fn [x]
                                  (if (= :require (and (seq? x) (first x)))
                                    (require+ (next x))
                                    x))
                                xs)))))

              (comment

                (require+ '([boot.nsub :as io]))

                (macroexpand '(ns bop
                                (:require [boot.nsub :as pop])))))

         #_(_
             (refer-clojure :exclude '[get])
             (use 'boot.prelude)



             (ns aze
               (:require [boot.prelude :as p]))

             (p/use!)

             (or [true nil] :io)

             (require '[boot.prelude :as p])
             (doseq [s '[assert not-empty empty or and cat]]
               (ns-unmap *ns* s))
             (ns-map *ns*)
             (p/use!))

         #_(do :def

               (defn duf
                 [{:keys [ns prefix name doc meta body]}]
                 (if prefix
                   `(nsub ~prefix (def ~name (do ~@body)))
                   `(def ~name (do ~@body))
                   ))

               (comment
                 (eval (duf {:name 'foo :body [42]}))
                 (eval (duf {:prefix 'foo.bar :name 'baz :body [42]}))
                 )))

(comment :cljs-xperiments

         (comment
           (defprotocol P1 (f1 [x]))
           (defrecord T1 [val])

           (macroexpand '(extend-type function P1 (f1 [x] :fn)))
           '(do (goog.object/set boot.nsub/P1 "function" true)
                (goog.object/set boot.nsub/f1 "function" (cljs.core/fn [x] :fn)))

           (macroexpand '(extend-type T1 P1 (f1 [x] :fn)))
           '(do
              (set! (. (. T1 -prototype) -boot$nsub$P1$) cljs.core/PROTOCOL_SENTINEL)
              (set! (. (. T1 -prototype) -boot$nsub$P1$f1$arity$1) (cljs.core/fn [x] (cljs.core/this-as x :fn))))

           (macroexpand '(def iop (cljs.core/fn ([x] x))))

           (f1 (fn []))
           (meta (var boot.nsub/f1))
           (println (var boot.nsub/P1))
           (js/console.log f1)
           (js/console.log (fn ([x] x) ([x y] y)))
           (goog.object/set boot.nsub/f1 "function" (fn [x] :over))

           (declare iop)
           (set! boot.prelude/iop "overiop")
           (do boot.prelude/iop)
           (declare mymy)

           (set! bootmymy/io 'op)
           )

         #?(:clj
            (defmac+ nsub

                     ;; expander
                     [name body ctx ns]
                     (let [fullname (n/dotsym ns ctx name)
                           ns-sym (n/dotsym ns ctx)
                           [ns-body decls] (split-with (comp keyword? first) body)]

                       ;; we have to keep track of subnamespaces in order to be able to know to which toplevel namespace they belong
                       ;; this way, when we will patch core/ns, we will be able to require recursively subnamespaces along with the required namespace
                       (swap! st/state
                              #(-> %
                                   (assoc-in [:namespaces fullname] #{})
                                   (update-in [:namespaces ns-sym] (fnil conj #{}) name)))


                       ;;#?(:clj (println (the-ns ns-sym)))
                       (p/pprob 'nsub-expand
                                `(do (~'ns ~fullname ~@ns-body)
                                     (~'require '[~ns-sym :refer ~(find-defs ns-body)])
                                     #_(~'use '~ns-sym)
                                     #_(~'use '[~ns-sym :exclude [~'self]])
                                     #_(~'use ['~ns-sym :exclude ['~'self]])
                                     (~'ns-unmap '~fullname '~'self)
                                     (declare ~'self)
                                     ~@(mapv (fn [e]
                                               (if (nsub-form? e)
                                                 (nsub-fn (update (nsub-parse (next e))
                                                                  :ctx conj name))
                                                 e))
                                             decls)
                                     (in-ns '~ns-sym)
                                     (require '[~fullname :as ~name])
                                     #_(require ['~fullname :as '~name])
                                     ~@(for [n (range (count ctx))]
                                         (let [ns-sym (n/dotsym ns (take n ctx))
                                               alias-sym (n/dotsym (drop n ctx) name)]
                                           `(do
                                              (in-ns '~ns-sym)
                                              (require '[~fullname :as ~alias-sym])
                                              #_(require ['~fullname :as '~alias-sym]))))
                                     (in-ns '~ns-sym)
                                     (def ~name ~(sym name "/self")))))

                     ;; parser
                     [name & body]
                     {:name name
                      :body body
                      :ns (ns-sym)
                      :ctx []}))

         #_(nsub aze
                 (:require [boot.prelude :as p #?@(:cljs [:include-macros true])])
                 (p/defn+ add [x & xs] (apply + x xs))
                 (defn self [& _] "i'm the aze sub module")
                 (nsub bop
                       (defn self [& _] "i'm the bop sub module")
                       (def loula 33))
                 (nsub lou
                       (def self "value module")))

         #_(p/assert
             (= 33 aze.bop/loula)
             (aze/bop)
             (= "value module" aze/lou))

         #_(keys (js->clj boot.named))

         #_(:clj (p/pp (macroexpand '(nsub aze
                                           (:require [boot.fn :as fn])
                                           (fn/defn add [x y] (+ x y))
                                           (defn self [& _] "i'm the aze sub module")
                                           (nsub bop
                                                 (defn self [& _] "i'm the bop sub module")
                                                 (def loula 33))
                                           (nsub lou
                                                 (def self "value module"))))))



         (comment
           (ns pop
             (:require [boot.prelude :as prel]))
           (def foo 42)
           (def $ #'prel/$)
           (defn t [] (println prel/iop) (println pop/foo))
           (println (pop/$ (range 5) inc))))

