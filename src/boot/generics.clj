(ns boot.generics
  (:require [boot.prelude :as p :refer [$ $vals sym pp]]
            [boot.types :as t]
            [boot.state :as state]
            [clojure.core :as c]
            [clojure.string :as str]))

;; generic function
;; based on clojure protocols with some extra features

;; generics can be variadics
;; generics can be extended by arity
;; (in regular protocols, you have to implement all arity when extending your proto to your type
;; even if a parent class already implement those...)
;; there is some shortcuts when 2 or more types share an implementation
;; via the set syntax litteral e.g #{:type1 :type2}
;; it works with asparagus.boot.types (which is a thin layer on top of clojure class hierarchy)



(do :state

    ;; a way to compile lambda case diferently if needed
    ;; used in 'with-compiled-cases if no overides given
    ;; you probably should not worry about that
    ;; currently only used in floor.core
    (def lambda-case-compiler* (atom identity))

    (defn get-reg []
      (state/get :fns))

    (defn get-spec [name]
      #_(println "resolve spec name " name (resolve name))
      (state/get-in [:fns (p/resolve-symbol name)]))

    (defn get-spec! [name]
      #_(p/pprob @state)
      (or (get-spec name)
          (p/error "Cannot find spec " name)))

    (defn reset-registry! []
      (swap! state/state assoc-in [:clj :fns] {})
      (swap! state/state assoc-in [:cljs :fns] {}))

    (reset-registry!))

(do :impl

    (defn with-ns
      ([sym]
       (with-ns *ns* sym))
      ([ns sym]
       (symbol (str ns) (str sym))))

    (defn derive-name_bu [n]
      {:name n
       :protocol-prefix (sym 'I n)
       :method-prefix (sym 'p_ n)
       :ns (p/ns-sym)
       :fullname (with-ns (name n))})

    (defn derive-name [n]
      (let [ns-str (or (namespace n) (str *ns*))
            ns (symbol ns-str)
            name-str (name n)
            name (symbol name-str)]
        {:ns ns
         :name name
         :protocol-prefix (sym 'I name)
         :method-prefix (sym 'p_ name)
         :fullname (symbol ns-str name-str)}))

    (defn arify-name [n a]
      (sym n '_ (str a)))

    (defn variadic-argv? [x]
      ((set x) '&))

    (defn bodify-fn-case [[pattern b1 & bs]]
      (list pattern (if-not bs b1 (list* 'do b1 bs))))

    (defn normalize-fn-cases [xs]
      (mapv bodify-fn-case
            (cond
              (vector? (first xs)) [xs]
              (every? seq? xs) (vec xs)
              :else (p/error "invalid fn cases:\n " xs))))

    (defn split-cases [xs]
      (let [{fixed nil
             variadic '&}
            (group-by (comp variadic-argv? first) xs)]
        (assert (#{0 1} (count variadic)))
        {:fixed fixed
         :variadic (first variadic)}))

    (defn format-variadic-case
      [[argv & members]]
      (cons (-> argv butlast butlast
                vec (conj (last argv)))
            members))

    (defn casemaps

      "(casemaps '([a b] :t1 e1 :t2 e2))
       ;;=>
       [{:type t1 :argv [a b] :arity 2 :expr e1}
        {:type t2 :argv [a b] :arity 2 :expr e2}]"

      [[argv & decls]]
      (let [arity (count argv)]
        (reduce
          (fn [a [t e]]
            (conj a {:type t :argv argv :arity arity :expr e}))
          [] (partition 2 decls))))

    (defn variadify-argv [v]
      (vec (concat (butlast v) ['& (last v)])))

    (defn parse-case [x]
      (let [cnt (count x)]
        (cond
          ;(= 1 cnt) (concat x [:any `(p/error "no implementation error")])
          (even? cnt) (concat (butlast x) [:any (last x)])
          :else x)))

    (defn parse-cases [xs]
      (map parse-case
           (if (vector? (first xs))
             (list xs)
             xs)))

    (p/assert
      (split-cases (parse-cases '(([a]) ([a & xs]))))
      (= (parse-cases '([a] :any 1))
         (parse-cases '(([a] 1))))
      (= (parse-cases '([a] :vec 1 1))
         (parse-cases '(([a] :vec 1 :any 1)))))

    (defn conj-case [cases case]
      (let [any? #(= :any (:type %))
            same-arity? #(= (:arity case) (:arity %))
            parent? #(t/parentof (:type case) (:type %))
            overiden-case? #(and (same-arity? %) (parent? %))
            remv (comp vec remove)]
        (if (any? case)
          (conj (remv any? cases) case)
          (conj (remv overiden-case? cases) case))))

    (defn case-name [name type arity]
      ;; for each case we build a uniq name that will hold this particular implementation
      ;; a def will be emitted holding it, and we will be able to inline it in some case
      ;; it also will simplify sharing
      (cond (set? type) (case-name name (apply p/sym (interpose "&" (sort type))) arity)
            (p/word? type) (p/sym (arify-name name arity) "_IMPL_" type)
            :else (p/error "bad type " type)))

    )

(do :parts

    (defn with-compiled-cases

      [{:as spec :keys [name ns cases]}
       & {:keys [lambda-case-compiler
                 extension-ns]}]

      (assoc spec
        :cases
        (mapv (fn [{:keys [arity type argv expr] :as casemap}]
                (let [dispatch-name (case-name name type arity)]
                  (assoc casemap
                    :ns ns
                    :name dispatch-name
                    :fullname (with-ns (or extension-ns ns) dispatch-name)
                    :compiled
                    ((or lambda-case-compiler @lambda-case-compiler*)
                     (list argv expr)))))
              (mapcat casemaps cases))))

    (defn expanded-cases [spec]
      (letfn
        [(expand-case [c]
           (map #(assoc c :type %) (t/classes (:type c))))
         (conj-case [cs c]
           (-> (remove #(= (:type %) (:type c)) cs) vec (conj c)))]
        (reduce conj-case []
                (mapcat expand-case (:cases spec)))))

    (defn extension-map [spec]
      (letfn [(expand-case [c]
                (map #(assoc c :type %) (t/classes (:type c))))
              (conj-case [m {:keys [type arity forkname fullname]}]
                (assoc m [type arity]
                         (merge (-> spec :arities (get arity))
                                {:arity arity
                                 :impl-name (or forkname fullname)})))]
        (reduce conj-case {} (mapcat expand-case (:cases spec)))))

    (defn with-arity-map

      [{:as spec :keys [cases protocol-prefix method-prefix]}]

      (assoc spec
        :arities
        (->> (map :arity cases)
             (into #{})
             (map (fn [arity]
                    [arity {:protocol-name (arify-name protocol-prefix arity)
                            :method-name (arify-name method-prefix arity)
                            :argv (p/argv-litt arity)}]))
             (into {}))))

    (defn with-arity-map

      [{:as spec :keys [cases protocol-prefix method-prefix]} arities]

      (assoc spec
        :arities
        (->> arities
             (map (fn [arity]
                    [arity {:protocol-name (arify-name protocol-prefix arity)
                            :method-name (arify-name method-prefix arity)
                            :argv (p/argv-litt arity)}]))
             (into {}))))

    (defn generic-spec [name body & {:keys [extension-ns lambda-case-compiler]}]

      (let [doc (when (string? (first body)) (first body))
            cases' (if doc (rest body) body)
            cases (parse-cases cases')
            {:keys [fixed variadic]} (split-cases cases)
            variadic (some-> variadic format-variadic-case)
            variadic-arity (some-> variadic first count)
            cases (if-not variadic fixed (concat fixed [variadic]))
            arities (into #{} (map (comp count first) cases))
            spec
            (as-> {:variadic? (boolean variadic)
                   :cases cases
                   :doc doc} X
                  (merge (derive-name name) X)
                  (with-compiled-cases
                    X
                    :extension-ns extension-ns
                    :lambda-case-compiler lambda-case-compiler)
                  (with-arity-map X arities))]

        (assert (if variadic (= variadic-arity (apply max (-> spec :arities keys))) true)
                "arity error, fixed arity > variadic arity")

        spec

        ))

    (defn fork-spec [parent-name fork-name]
      (let [names (derive-name fork-name)
            parent-spec (get-spec! parent-name)
            ns (p/ns-sym)
            forked-case
            (fn [{:as c :keys [forkname fullname type arity]}]
              (-> (dissoc c :fullname)
                  (assoc :ns ns
                         :name (case-name fork-name type arity)
                         :forkname (or forkname fullname))))]
        (with-arity-map
          (update (merge parent-spec names)
                  :cases (fn [cs] (mapv forked-case cs)))
          (set (keys (:arities parent-spec))))))

    (defn dispatches-declarations [spec]

      (->> (:cases spec)
           (map (fn [{:keys [forkname compiled name]}]
                  (if forkname
                    (do (assert (resolve forkname)
                                (str forkname " is not available in " (p/ns-sym)))
                        `(def ~name ~forkname))
                    `(defn ~name ~compiled))))
           (list* 'do)))

    (comment (dispatches-declarations (get-spec! 'g1)))

    (comment :backup
             (defn extend-forms
               [{:as spec :keys [ns arities cases]}]

               (doall
                 (mapcat
                   (fn [{:as case :keys [type arity compiled]}]
                     (map (fn [k]
                            (let [{:keys [protocol-name method-name]} (arities arity)]
                              (list `c/extend k
                                    (with-ns ns protocol-name)
                                    {(keyword method-name)
                                     (list `fn compiled)})))
                          (t/classes type)))
                   cases)))

             (defn extend-type-forms
               [{:as spec :keys [ns arities cases]}]

               (doall
                 (mapcat
                   (fn [{:as case :keys [type arity compiled]}]
                     (map (fn [k]
                            (let [{:keys [protocol-name method-name]} (arities arity)]
                              (list `extend-type k
                                    (with-ns ns protocol-name)
                                    (list method-name compiled))))
                          (t/classes type)))
                   cases))))

    (defn extend-forms [{:as spec :keys [ns]}]
      (mapv
        (fn [[[class arity] {:keys [protocol-name method-name impl-name]}]]
          (list `c/extend class
                (with-ns ns protocol-name)
                {(keyword method-name) impl-name}))
        (extension-map spec)))

    (defn extend-type-forms [{:as spec :keys [ns]}]
      (mapv
        (fn [[[class arity] {:keys [protocol-name method-name impl-name]}]]
          (let [argv (p/argv-litt arity)]
            (list `extend-type class
                  (with-ns ns protocol-name)
                  (list method-name argv (list* impl-name argv)))))
        (extension-map spec)))

    (defn registering-form [spec]
      #_(println 'willswap [:fns (if p/*cljs* :cljs :clj) (:name spec)] #_spec)
      (state/swap! assoc-in [:fns (:fullname spec)] spec)
      #_(println get-reg)
      #_(println `(swap! state assoc-in [:fns '~(:name spec)] '~spec))
      nil)

    (defn extend-spec
      [spec extension-spec]

      (assert (every? (or (-> spec :arities keys set)
                          (fn [x] (println "should not be here (generics/extend-spec") true))
                      (-> extension-spec :arities keys))
              "unknown arity")

      (update spec :cases
              (fn [cs] (reduce conj-case cs (:cases extension-spec)))))


    (defn protocol-declaration-form
      [{:keys [arities ns]}]
      `(do ~@(mapv (fn [[arity {:keys [protocol-name method-name argv]}]]
                     `(defprotocol ~(with-ns ns protocol-name)
                        ~(list method-name argv)))
                   arities)))

    (defn protocol-extension-form
      [spec]
      (if (state/cljs?)
        `(do ~@(extend-type-forms spec))
        `(do ~@(extend-forms spec))))

    (defn function-definition-form
      [{:keys [name arities variadic?]}]
      (let [arities (sort arities)
            fixed-arities (if variadic? (butlast arities) arities)
            ]
        `(defn ~name
           ~@(mapv (fn [{:keys [argv method-name]}] `(~argv (~method-name ~@argv)))
                   (vals fixed-arities))
           ~@(when variadic?
               (let [variadic-arity (val (last arities))
                     vsig (:argv variadic-arity)]
                 [`(~(variadify-argv vsig) (~(:method-name variadic-arity) ~@vsig))])))))

    (defn protocol-initialisation-form [spec]
      `(do ~(protocol-declaration-form spec)
           ~(protocol-extension-form spec)))

    #_(defn extension-form [spec]
        #_(pp "extform" (get-spec! (:name spec)))
        (let [spec+ (extend-spec (get-spec! (:name spec)) spec)]
          (registering-form spec+)
          (protocol-extension-form spec+)))

    (defn extension-form [spec]
      #_(pp "extform" (get-spec! (:name spec)))
      (registering-form (extend-spec (get-spec! (:fullname spec)) spec))
      `(do ~(dispatches-declarations spec)
           ~(protocol-extension-form spec)))

    (defn cleaning-form [{:as s :keys [ns name arities]}]
      `(do
         ~@(mapv (fn [x#] `(ns-unmap '~(symbol ns) '~x#))
                 (cons name (mapcat (juxt :method-name :protocol-name) (vals arities))))))

    (defn declaration-form [spec]
      #_(println p/*cljs*)
      (registering-form spec)
      `(do ~(cleaning-form spec)
           ~(protocol-declaration-form spec)
           ~(function-definition-form spec)
           ~(dispatches-declarations spec)
           ~(protocol-extension-form spec)
           ~(:name spec)))

    )

(do :refresh

    (defn implementers
      "given a generic spec,
       returns a vector of all types that implement the corresponding generic"
      [spec]
      (->> (:cases spec)
           (map (fn [case]
                  (reduce (fn [a e]
                            (if (set? e) (into a e) (conj a e)))
                          #{} (map :type case))))
           (reduce into #{})))

    (defn implementers-map []
      ($vals (get-reg) implementers))

    (defn sync-spec!
      "recompile and execute the spec of the given name"
      [name]
      #_(println "refreshing generics: " name)
      (eval (extension-form (get-spec! name))))

    (defn sync-types!
      "when type registry has been updated,
       we sometimes need to sync some generics declaration
       xs: the types that have changed
       only the generics impacted by this change will be synced"
      [xs]
      (let [sync? #(seq (clojure.set/intersection (set xs) (set %)))]
        (doseq [[name ts] (implementers-map)]
          #_(pp 'generics/sync-types name)
          (when (sync? ts) (sync-spec! name)))))

    (defn sync-types-form
      "when type registry has been updated,
       we sometimes need to sync some generics declaration
       xs: the types that have changed
       only the generics impacted by this change will be synced"
      [xs]
      (let [sync? #(seq (clojure.set/intersection (set xs) (set %)))]
        (cons 'do
              (keep (fn [[name ts]]
                      (when (sync? ts)
                        (extension-form (get-spec! name))))
                    (implementers-map)))))

    #_(sync-types! [:num :str])

    )



(do :api

    ;; user API, see concrete usage in tests below

    (p/defmac generic
      "create a generic function"
      [name & cases]
      (declaration-form
        (generic-spec name cases)))

    (p/defmac reduction
      ([name case]
       `(reduction ~name ~@case))
      ([name x & xs]
       `(generic ~name
                 ([x#] x#)
                 (~x ~@xs)
                 ([x# y# & others#]
                  :nil (reduce ~name (~name x# y#) others#)
                  :any (reduce ~name (~name x# y#) others#)))))

    (p/defmac generic+
      "add new cases to an existant generic
       all given arities must already be known"
      [name & cases]
      (extension-form
        (generic-spec (p/resolve-symbol name)
                      cases
                      :extension-ns (p/ns-sym))))



    (p/defmac fork
      "create a new generic from an existing one
       does not alter the original"
      [parent-name name & cases]
      (let [spec (fork-spec parent-name name)
            extension-spec (generic-spec name cases)
            spec (extend-spec spec extension-spec)]
        (declaration-form spec)))

    (p/defmac implements?
      "test if something implements a generic"
      ([v name]
       (let [gspec (get-spec! name)
             vsym (gensym)]
         `(let [~vsym ~v]
            (when (or ~@(mapv (fn [protocol-name] `(satisfies? ~(with-ns (:ns gspec) protocol-name) ~vsym))
                              (map (comp :protocol-name val) (:arities gspec))))
              ~vsym))))
      ([v name & names]
       (let [vsym (gensym)]
         `(let [~vsym ~v]
            (and ~@(map (fn [n] `(implements? ~vsym ~n)) (cons name names)))))))

    (p/defmac compile-all!
      [] `(do ~@(map protocol-extension-form (vals (get-reg)))))

    (do :type+

        (defn implement_impl-body->cases_deprecated
          [tag [x1 & xs :as all]]
          (let [bodify (fn [[b1 & bs]]
                         (if-not bs b1
                                    (list* 'do b1 bs)))]
            (if (vector? x1)
              [(list x1 tag (bodify xs))]
              (map (fn [[argv & bs]]
                     (list argv tag (bodify bs)))
                   all))))

        (defn implement_impl-body->cases
          [tag cases]
          (map (fn [[pat bod]] (list pat tag bod))
               (normalize-fn-cases cases)))

        (defn implement [tag [name & body :as form]]

          (if (get-spec name)
            `(generic+ ~name ~@(implement_impl-body->cases tag body))
            ;; TODO do I want to restore that ? it does not works well with refreshing
            (if-let [p (-> (resolve name) meta :protocol)]
              `(extend-protocol ~(symbol p)
                 ~@(doall (mapcat (fn [t] [t form]) (t/classes tag)))))))

        (p/defmac type+
          "like extend type"
          [tag & impls]
          `(do ~@(mapv #(implement tag %) impls))))

    (do :thing

        (defn thing_parse-impl-cases
          [[name & cases]]
          (let [{:as spec :keys [method-prefix protocol-prefix]}
                (get-spec! name)
                with-clean-pattern
                (fn [x] (update x :pattern (comp vec (partial remove #{'&}))))
                with-variadic-flag
                (fn [x] (assoc x :variadic (variadic-argv? (:pattern x))))
                with-names
                (fn [x]
                  (let [ari (count (:pattern x))]
                    (assoc x :arity ari
                             :method-name (arify-name method-prefix ari)
                             :protocol-name (arify-name protocol-prefix ari))))]

            (->> (normalize-fn-cases cases)
                 (map (fn [[pat bod]] {:pattern pat :body bod}))
                 (map with-variadic-flag)
                 (map with-clean-pattern)
                 (map with-names))))

        (defn thing_cases->decls [xs]
          (mapcat (fn [{:keys [method-name protocol-name body pattern]}]
                    [protocol-name (list method-name pattern body)])
                  xs))

        (p/defmac thing
          "like reify but for generics"
          [& impls]
          `(reify
             ~@(mapcat thing_cases->decls
                       (map thing_parse-impl-cases impls)))))

    )

(do :extension

    (defn conj-type [reg {:keys [tag childs parents]}]
      (reduce
        (fn [reg p]
          (update reg p (fnil conj #{}) tag))
        (update reg tag (fnil into #{}) childs)
        parents))

    (p/defmac tag+

      "add a type tag to the type registry (living in asparagus.boot.state/state)
       tag: the typetag we are defining/extending (a keyword)
       childs: a seq of other typetags or classes that belongs to the defined tag
       parents: a seq of other typetags that the defined tag belongs to
       & impls: optional generic implementations for the defined tag"

      ([{:keys [tag childs parents impls]}]
       (let [exists? (state/get-in [:types tag])
             generic-updates
             (if exists? (cons tag parents) parents)]

         (state/swap!
           update :types
           conj-type
           {:tag tag
            :childs childs
            :parents parents})

         ;; this is brutal, should only recompute what's nescessary
         (state/swap! assoc :guards (t/predmap))

         `(do
            ~(sync-types-form (vec generic-updates))
            ~(when (seq impls) `(type+ ~tag ~@impls)))))

      ([tag childs]
       `(tag+ ~tag ~childs []))
      ([tag childs parents & impls]
       `(tag+ ~{:tag tag :childs childs :parents parents :impls (vec impls)})))

    (p/defmac deft

      "declare a new usertype (a clojure record)
       tag: the typetag (keyword) corresponding to our freshly created record
       fields: the fields of our record
       parents: a seq of other typetags that our type belongs to
       & impls: optional generic implementations for the defined type"

      ([{:as spec
         :keys [tag parents impls fields childs class-sym]}]
       (let [class-str (apply str (map str/capitalize (str/split (name tag) #"\.")))
             class-sym (or class-sym (symbol class-str))
             spec (update spec :childs (fnil conj []) class-sym)]
         `(do (defrecord ~class-sym ~fields)
              (def ~(symbol tag) ~(p/sym '-> class-sym))
              (generic ~(p/sym '-> (name tag)) [~'_])
              (tag+ ~spec))))
      ([tag fields]
       `(deft ~tag ~fields []))
      ([tag fields x & xs]
       (let [[parents impls]
             (if (vector? x) [x xs] [[] (cons x xs)])]
         `(deft ~{:tag (keyword tag) :parents parents
                  :impls (vec impls) :fields fields})))))



(comment

  (get-reg)
  (tag+ :iop.fop [:vec :set] [:hash])

  (do :implements?-test
      (generic gg1 [x y] :vec [:gg1-vec x y])
      (generic gg2 [x] [:gg2 x])
      (generic gg3 [x] :str [:gg3-str x])
      (get-spec! 'gg1)
      (implements? 1 gg1)
      (implements? [] gg1 gg2)
      (implements? [] gg1 gg2 gg3))

  (do :thing-test

      (generic gg2 ([x] 42) ([x y] :vec [:gg2-vec x y])
               ([x y & others] [:gg2-variad x y others]))

      (macroexpand-1
        '(thing (gg1 [a b] ::pouet)
                (gg2 ([x] :1) ([x y] ::yop) ([x y & zs] ::popopo)))))

  (t/classes :map)

  (macroexpand '(tag+ :iop.fop [:vec :set] [:hash]))

  (deft :pou.pouet [iop foo] nil
        #_(g1 [x] "g1foo"))

  (deft {:tag :pouet
         :fields [iop foo]
         :class-sym POUUUUUET
         #_(g1 [x] "g1foo")}))

