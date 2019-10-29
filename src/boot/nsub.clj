(ns boot.nsub
  (:use boot.prelude)
  (:require ;;[ns-tracker.core :as nst]
            [clojure.core :as c]
            [clojure.string :as str]))

(defn dotsym
  ([x]
   (cond
     (= "" x) nil
     (string? x) (symbol x)
     (word? x) (dotsym (name x))
     (sequential? x)
     (when (seq x)
       (dotsym (str/join "." (remove nil? (map dotsym x)))))))
  ([x & xs]
   (dotsym (cons x xs))))

(defn ns-sym [] (symbol (str *ns*)))

(do :defmac+

    (defn parse-defmac+ [[name & [x & xs]]]
      (let [[doc [x & xs]] (if (string? x) [x xs] ["no doc" (cons x xs)])
            [meta [keys expansion & xs]] (if (map? x) [x xs] [{} (cons x xs)])
            parse-cases (cond (seq? (first xs)) xs
                              (second xs) (list xs)
                              :else
                              (let [argv (or (first xs) keys)
                                    ss (shadows argv)]
                                [(list argv (zipmap (map keyword ss) ss))]))]
        {:doc doc
         :meta meta
         :name name
         :keys (vec (shadows keys))
         :expansion expansion
         :parse-cases parse-cases}))

    (do :asserts
        (is (parse-defmac+ '(iop [a b c & xs] (pouet)))
            '{:doc "no doc",
              :meta {},
              :name iop,
              :keys [a xs c b],
              :expansion (pouet),
              :parse-cases [([a b c & xs] {:a a, :xs xs, :c c, :b b})]})
        (is (parse-defmac+ '(iop [a b c xs] (pouet) [b a c & xs]))
            '{:doc "no doc",
              :meta {},
              :name iop,
              :keys [a xs c b],
              :expansion (pouet),
              :parse-cases [([b a c & xs] {:a a, :xs xs, :c c, :b b})]})
        (is (parse-defmac+ '(iop "foo" {:me :ta} [a b c] (pouet) ([x] 'iop) ([x & xs] 'pouet)))
            '{:doc "foo",
              :meta {:me :ta},
              :name iop,
              :keys [a c b],
              :expansion (pouet),
              :parse-cases (([x] 'iop) ([x & xs] 'pouet))}))

    (defmacro defmac+

      "personal defmacro
       define a regular macro
       but also a function that do the same thing as the macro (when receiving quoted args)
       "

      ([{:as opts :keys [name keys doc meta expansion parse-cases]}]
       #_(println opts)
       (let [fname (sym name '-fn)
             fname* (sym fname '*)
             predname (sym name '-form?)
             expname (sym name '-xp)
             exprecname (sym name '-xprec)
             parser (sym name '-parse)]

         `(do
            ;; parser
            (defn ~parser [x#]
              (apply (fn ~@parse-cases) x#))

            ;; function
            (defn ~fname
              ([{:keys ~keys}] ~expansion)
              ([x# & xs#] (~fname (~parser (cons x# xs#)))))

            (def ~fname* (p* ~fname))

            ;; pred
            (defn ~predname [x#]
              (and (seq? x#) (= '~name (first x#))))

            ;; expansion
            (defn ~expname [x#]
              (if (~predname x#)
                (~fname* (next x#))
                x#))

            (defn ~exprecname [x#]
              (cond (~predname x#) (~expname x#)
                    (sequential? x#) ($ x# ~expname)
                    :else x#))
            ;; macro
            (defmacro ~name [& xs#]
              (~fname* xs#)))))

      ([x & xs]
       `(defmac+ ~(parse-defmac+ (cons x xs)))))

    (comment
      (mx' (defmac+ iop [a b] (list b a)))

      (mx' (defmac+ dfn [name doc cases]
             `(defn ~name ~(or doc "") ~@cases)
             ([& xs]
              (parse-fn xs))))

      (mx' (defmac+ dfn [name & body]
             `(defn ~name ~@body)))

      (dfn hello "says hello" ([] "yo") ([x] (str "hey" x)))
      (dfn-parse '(hello "says hello" ([] "yo") ([x] (str "hey" x))))
      ))

(do :old-impl
 (def ^:dynamic *ns-str* (str *ns*))
 (defmac nsub
   [name & body] 
   (let [ns-str (str *ns*)
         parent-sym (symbol *ns-str*)
         extra-segments
         (drop (count (sym-split ns-str))
               (sym-split parent-sym))
         fullname (sym parent-sym '. name)
         [ns-body decls] (split-with (comp keyword? first) body)]
    
     `(do (ns ~fullname ~@ns-body)
          (~'use ['~parent-sym :exclude ['~'self]])
          (declare ~'self)
          ~@(binding [*ns-str* (c/name fullname)]
              #_(println "hey" *ns-str*)
              (concat (mapv mx decls)
                      `[(in-ns '~parent-sym)
                        (require ['~fullname :as '~name])
                        ~@(for [n (range (count extra-segments))]
                            (let [ns-sym (dotsym ns-str (take n extra-segments))
                                  alias-sym (dotsym (drop n extra-segments) name)]
                              `(do
                                 (in-ns '~ns-sym)
                                 (require ['~fullname :as '~alias-sym]))))
                        (in-ns '~parent-sym)
                        (def ~name ~(sym name "/self"))]))))))

(do :nsub

    (defmac+ nsub

      ;; expander
      [name body ctx ns]
      (let [fullname (dotsym ctx name)
            [ns-body decls] (split-with (comp keyword? first) body)
            extra-segments (drop (count (sym-split ns)) (sym-split ctx))
            ]
        `(do (ns ~fullname ~@ns-body)
             (~'use ['~ctx :exclude ['~'self]])
             (declare ~'self)
             ~@(mapv (fn [e]
                       (if (nsub-form? e)
                         (nsub-fn (assoc (nsub-parse (next e))
                                         :ctx fullname))
                         e))
                     decls)
             (in-ns '~ctx)
             (require ['~fullname :as '~name])
             ~@(for [n (range (count extra-segments))]
                 (let [ns-sym (dotsym ns (take n extra-segments))
                       alias-sym (dotsym (drop n extra-segments) name)]
                   `(do
                      (in-ns '~ns-sym)
                      (require ['~fullname :as '~alias-sym]))))
             (in-ns '~ctx)
             (def ~name ~(sym name "/self"))))

      ;; parser
      [name & body]
      {:name name
       :body body
       :ns (ns-sym)
       :ctx (ns-sym)})

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

        (assert
         (is 33 aze.bop/loula)
         (aze/bop)
         (is "value module" aze/lou))))
