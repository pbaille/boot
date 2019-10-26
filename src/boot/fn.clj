(ns boot.fn
  (:refer-clojure :exclude [fn defn fn? compile]))

(alias 'c 'clojure.core)

(c/defn conform [[fst & nxt :as all]]

  (let [default-name (gensym "fn_")
        [name fst & nxt]
        (if (symbol? fst)
          (cons fst nxt)
          (concat [default-name fst] nxt))

        [doc fst & nxt]
        (if (string? fst)
          (cons fst nxt)
          (concat ["" fst] nxt))

        [opts fst & nxt]
        (if (map? fst)
          (cons fst nxt)
          (concat [{} fst] nxt))

        impls
        (if (vector? fst)
          {fst (vec nxt)}
          (into {}
                (map
                  (c/fn [[args & body]]
                    [args (vec body)])
                  (cons fst nxt))))

        name-key
        (if (= default-name name)
          :default-name
          :name)]

    (assoc opts
      name-key name
      :doc doc
      :impls impls)))

(comment
  (conform
    '([b] b))

  (conform
    '(([b] b)
       ([a b] (/ a (+ a b)))))

  (conform
    '(yop [b] b))

  (conform
    '(yop
       ([b] b)
       ([a b] (/ a (+ a b)))))

  (conform
    '(yop {:foo :bar}
          [b] b))

  (conform
    '(yop {:foo :bar}
          ([b] b)
          ([a b] (/ a (+ a b))))))

(defmacro fn [& form]
  (let [locals (keys &env)
        {:keys [impls name default-name] :as met} (conform form)]
    `(with-meta (~'clojure.core/fn ~(or name default-name) ~@(map (partial apply list*) impls))
                (assoc '~met
                  :type 'fn
                  :code '~&form
                  :locals (zipmap '~locals ~(vec locals))))))

(comment
  (macroexpand '(fn [b] b))
  (macroexpand '(fn {:meta 1} [b] b))
  (macroexpand '(fn [b] b))
  (fn [b] b)

  (let [b 1
        f (c/fn [a] a)]
    (a b))

  (clojure.walk/macroexpand-all '(c/fn [b] b))

  (let [z 1]
    (def a (fn [b] b)))

  (a 12)
  (meta a)

  (macroexpand (let [a 1
                     f (fn [b] a)]
                 (meta f)))
  (macroexpand (let [a 1] '(fn [b] a)))
  (fn [b] b)

  (meta (fn ([b] b)
             ([a b] (/ a (+ a b)))))

  (meta (fn yop [b] b))

  (meta (fn yop
             ([b] b)
             ([a b] (/ a (+ a b)))))

  (meta (fn yop {:foo :bar}
             [b] b))

  (meta )

  (meta (fn yop {:foo :bar}
             ([b] b)
             ([a b] (/ a (+ a b))))))

(defmacro defn [& form]
  (let [{:keys [name]} (conform form)]
    `(def ~name (fn ~@form))))

(c/defn fn? [x]
  (-> x meta :type (= 'fn)))

(comment
  (macroexpand '(f* iop [o] o))
  (meta (f* iop [o] o))
  (defn aze
        "iop"
        {:o :c}
        ([a] a)
        ([a b] b)
        ([a b & c] :pouet)))

(c/defn show [f]
  (let [{:keys [show code locals name] :as m} (meta f)]
    (cond
      ;; native funs
      (not m)
      (-> (str f)
          (clojure.string/split #"@")
          first
          symbol)

      show
      (if (c/fn? show) (show m) show)

      name name

      (seq locals)
      {:locals locals :code code}

      :else code)))

;define getters
(eval
  `(do
     ~@(map
         (c/fn [x]
           `(~'def ~x #(-> % meta ~(keyword (name x)))))
         '[impls
           code
           doc
           locals])))

(c/defn arity-map [f]
  (into {}
        (map (c/fn [[args & body]]
               [(if ((set args) '&)
                  (dec (count args))
                  (count args))
                {:args args
                 :body (vec body)}])
             (impls f))))

(c/defn polyadic? [f]
  (next (impls f)))

(c/defn variadic? [f]
  (let [am (arity-map f)
        maxa (apply max (keys am))]
    ((-> (am maxa) :args set) '&)))

(c/defn arity [f]
  (and (not (polyadic? f))
       (not (variadic? f))
       (-> (impls f) first key count)))

(c/defn arities [f]
  (->> (arity-map f)
       keys
       sort))

(c/defn varity [f]
  (and (variadic? f)
       (dec (last (arities f)))))

(c/defn min-arity [f]
  (if (and (variadic? f)
           (not (polyadic? f)))
    (varity f)
    (first (arities f))))

(c/defn max-arity [f]
  (when-not (variadic? f)
    (last (arities f))))

(c/defn has-arity? [f n]
  (or
    ((arity-map f) n)
    (when-let [va (varity f)] (<= va n))))

(c/defn has-partial-arity? [f n]
  (let [am (arity-map f)]
    (and (not (am n))
         (< n (or (max-arity f)
                  (varity f))))))

(comment
  (arity (fn [a] a))
  (arities (fn [a] a))
  (arities (fn ([a] a) ([a b] a) ([a b & [aze]] a)))
  (varity (fn ([a] a) ([a b] a) ([a b & [aze]] a)))
  (varity (fn ([a] a) ([a b] a))))

(c/defn split-args [f args]
  (let [acnt (count args)
        maxa (max-arity f)]

    (cond
      (or (has-arity? f acnt)
          (has-partial-arity? f acnt))
      [args []]

      (and maxa (> acnt maxa))
      (split-at maxa args))))

;; not compatible with cljs
(defmethod print-method clojure.lang.Fn [f w]
  (print-method (show f) w))

(defmethod print-method clojure.lang.AFunction [f w]
  (print-method (show f) w))

(c/defn locals->bindings [f]
  (vec (mapcat identity (locals f))))

(c/defn form [f]
  (let [{:keys [doc name impls] :as m} (meta f)
        new-meta (dissoc m :doc :name :impls :locals :code :type :default-name)]
    `(~'let ~(locals->bindings f)
       (fn ~@(if name [name])
           ~@(if (seq doc) [doc])
           ~@(if (seq new-meta) [new-meta])
           ~@(map (partial apply list*) (sort-by (comp count key) impls))))))

(comment
  (eval (form (let [e 1] (fn [a b] 1 2 3)))))

(defn- compile [f]
  (println "compile: " (form f))
  (eval (form f)))

(comment
  (form (fn [c] (+ c c)))
  (form
    (compile
      (let [a 1]
        (fn [b] (fn [c] (+ a b c)))))))

(c/defn swap-impls [f g & args]
  (compile
    (vary-meta f update :impls #(apply g % args))))

(c/defn set-impls [f xs]
  (compile
    (vary-meta f assoc :impls xs)))

(c/defn merge-impls [fun imap]
  (let [overloaded-arities (set (map count (keys imap)))
        remaining-impls
        (into {}
              (remove
                (c/fn [[args _]]
                  (overloaded-arities (count args)))
                (-> fun meta :impls)))]
    (set-impls fun (merge remaining-impls imap))))

(comment
  (let [f (fn [a] a)
        f2 (set-impls f {'[a] ['(+ a a)]})
        ;; this will cause an error...
        f3 (let [c 4] (swap-impls f merge '{[a b] [(+ a b c)]}))
        f4 (merge-impls f3 '{[z] [(+ 1 z)]
                             [c d] [(* c d)]})
        ]
    [f
     (f 1)
     f2
     (f2 1)
     f3
     (f3 1)
     (f3 2 3)
     f4
     (f4 1)
     (f4 3 3)
     ]))

(def method-map
  {:variadic? variadic?
   :polyadic? polyadic?
   :arity arity
   :arity-map arity-map
   :compile compile
   :swap-impls swap-impls
   :set-impls set-impls})

(comment
  (let [x 1]
    ((c/fn f [a]
       (locals
         (fn g [b] [f (+ x a)])))
      1)
    )

  (c/fn [a] a)

  ((c/fn f [] (c/fn g [a] f)))

  (((eval `(c/fn ~'f [] (c/fn ~'g [~'a] ~'f)))
     )
    1)

  ((c/fn [a] a)))
