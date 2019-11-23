(ns boot.nsub
  (:require
   [clojure.core :as c]
   [clojure.string :as str]
   [boot.prelude :as p]
   [boot.named :as n]
   [boot.state :as st]))

(p/use!)

(do :nsub

    (defmac+ nsub

      ;; expander
      [name body ctx ns]
      (let [fullname (n/dotsym ns ctx name)
            ns-sym (n/dotsym ns ctx)
            [ns-body decls] (split-with (comp keyword? first) body)]

        (swap! st/state
               #(-> %
                    (assoc-in [:namespaces fullname] #{})
                    (update-in [:namespaces ns-sym] (fnil conj #{}) name)))

        `(do (ns ~fullname ~@ns-body)
             (~'use ['~ns-sym :exclude ['~'self]])
             (declare ~'self)
             ~@(mapv (fn [e]
                       (if (nsub-form? e)
                         (nsub-fn (update (nsub-parse (next e))
                                          :ctx conj name))
                         e))
                     decls)
             (in-ns '~ns-sym)
             (require ['~fullname :as '~name])
             ~@(for [n (range (count ctx))]
                 (let [ns-sym (n/dotsym ns (take n ctx))
                       alias-sym (n/dotsym (drop n ctx) name)]
                   `(do
                      (in-ns '~ns-sym)
                      (require ['~fullname :as '~alias-sym]))))
             (in-ns '~ns-sym)
             (def ~name ~(sym name "/self"))))

      ;; parser
      [name & body]
      {:name name
       :body body
       :ns (ns-sym)
       :ctx []})

    (do :tests

        (nsub aze
              (:require [boot.fn :as fn])
              (fn/defn add [x y] (+ x y))
              (defn self [& _] "i'm the aze sub module")
              (nsub bop
                    (defn self [& _] "i'm the bop sub module")
                    (def loula 33))
              (nsub lou
                    (def self "value module")))

        (swap! st/state dissoc :namespaces)

        (:namespaces @st/state)

        (assert
         (= 33 aze.bop/loula)
         (aze/bop)
         (= "value module" aze/lou))))

(_
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

(do :def

    (defn duf
      [{:keys [ns prefix name doc meta body]}]
      (if prefix
        `(nsub ~prefix (def ~name (do ~@body)))
        `(def ~name (do ~@body))
        ))

    (comment
      (eval (duf {:name 'foo :body [42]}))
      (eval (duf {:prefix 'foo.bar :name 'baz :body [42]}))
      ))

(_ :ns

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

    (defonce ns-impl @#'ns)

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



