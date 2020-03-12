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

    (defn get-reg []
      (state/get :fns))

    (defn get-spec [name]
      #_(println "resolve spec name " name (resolve name))
      (state/get-in [:fns (p/var-symbol (resolve name))]))

    (defn get-spec! [name]
      #_(p/pprob @state)
      (or (get-spec name)
          (p/error "Cannot find spec " name)))

    (defn reset-registry! []
      (swap! state/state assoc-in [:clj :fns] {})
      (swap! state/state assoc-in [:cljs :fns] {}))

    (reset-registry!))

(do :impl

    (defn arities [cases]
      (->> cases (map first) (map count) set))

    (defn with-ns [ns sym]
      (symbol ns (str sym)))

    (defn derive-name [n]
      {:name n
       :pname (sym 'I n)
       :mname (sym 'p_ n)
       :ns (str *ns*)
       :fullname (symbol (str *ns*) (name n))})

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
          [] (reverse (partition 2 decls)))))

    (defn variadify-argv [v]
      (vec (concat (butlast v) ['& (last v)])))

    (defn parse-case [x]
      (if (even? (count x))
        (concat (butlast x) [:any (last x)])
        x))

    (defn parse-cases [xs]
      (map parse-case
           (if (vector? (first xs))
             (list xs)
             xs)))

    (p/assert
      (= (parse-cases '([a] :any 1))
         (parse-cases '(([a] 1))))
      (= (parse-cases '([a] :vec 1 1))
         (parse-cases '(([a] :vec 1 :any 1))))))

(do :parts

    (defn compile-cases

      [{:as spec :keys [cases]}
       & [lambda-case-compiler]]

      (assoc spec
        :compiled-cases
        (mapv (fn [{:keys [argv expr] :as casemap}]
                (assoc casemap :compiled
                               ((or lambda-case-compiler identity)
                                (list argv expr))))
              (mapcat casemaps cases))))

    (defn generic-spec [name body]

      (let [doc (when (string? (first body)) (first body))
            cases' (if doc (rest body) body)
            cases (parse-cases cases')
            {:keys [fixed variadic]} (split-cases cases)
            variadic (some-> variadic format-variadic-case)
            variadic-arity (some-> variadic first count)
            argvs (concat (map first fixed) (some-> variadic first vector))
            arities (set (map count argvs))
            cases (if-not variadic fixed (concat fixed [variadic]))]

        (assert (if variadic (= variadic-arity (apply max arities)) true)
                "arity error, fixed arity > variadic arity")

        (merge
          (derive-name name)
          {:variadic? (boolean variadic)
           :arities arities
           :sigs (map p/argv-litt arities)
           :cases cases
           :doc doc})))

    (def compiled-generic-spec
      (comp compile-cases generic-spec))

    (defn extend-forms
      [{:as spec :keys [ns pname mname compiled-cases]}]

      (doall
        (mapcat
          (fn [{:as case :keys [type arity compiled]}]
            (map (fn [k]
                   (list `c/extend k
                         (with-ns ns (arify-name pname arity))
                         {(keyword (arify-name mname arity))
                          (list `fn compiled)}))
                 (t/classes type)))
          compiled-cases)))

    (defn extend-type-forms
      [{:as spec :keys [ns pname mname compiled-cases]}]

      (doall
        (mapcat
          (fn [{:as case :keys [type arity compiled]}]
            (map (fn [k]
                   (list `extend-type k
                         (with-ns ns #_(str *ns*) (arify-name pname arity))
                         (list (arify-name mname arity) compiled)))
                 (t/classes type)))
          compiled-cases)))

    (defn registering-form [spec]
      #_(println 'willswap [:fns (if p/*cljs* :cljs :clj) (:name spec)] #_spec)
      (state/swap! assoc-in [:fns (:fullname spec)] spec)
      #_(println get-reg)
      #_(println `(swap! state assoc-in [:fns '~(:name spec)] '~spec))
      nil)

    (defn extend-spec
      [spec extension-spec]
      #_(pp "extspec" [(:arities spec) (:arities extension-spec)])
      (p/assert (every? (:arities spec (constantly true)) (:arities extension-spec))
                "unknown arity")

      #_(merge-with
          concat spec
          (select-keys extension-spec
                       [:cases :compiled-cases]))

      (merge-with
        (fn [s1 s2]
          (concat (remove (set s2) s1) s2))
        spec
        (select-keys extension-spec
                     [:cases :compiled-cases])))


    (defn protocol-declaration-form
      [{:keys [pname mname sigs ns]}]
      `(do ~@(mapv (fn [argv]
                     (let [arity (count argv)]
                       `(defprotocol ~(with-ns ns (arify-name pname arity))
                          ~(list (arify-name mname arity) argv))))
                   sigs)))

    (defn protocol-extension-form
      [spec]
      (if (state/cljs?)
        `(do ~@(extend-type-forms spec))
        `(do ~@(extend-forms spec))))

    (defn function-definition-form
      [{:keys [name pname mname
               sigs variadic? arities]}]
      (let [sigs (sort sigs)
            fixed-sigs (if variadic? (butlast sigs) sigs)
            vsig (last sigs)
            vsig-argv (variadify-argv vsig)]
        `(defn ~name
           ~@(mapv (fn [sig] `(~sig (~(arify-name mname (count sig)) ~@sig)))
                   fixed-sigs)
           ~@(when variadic?
               [`(~vsig-argv (~(arify-name mname (count vsig)) ~@vsig))]))))

    (defn protocol-initialisation-form [spec]
      `(do ~(protocol-declaration-form spec)
           ~(protocol-extension-form spec)))

    (defn extension-form [spec]
      #_(pp "extform" (get-spec! (:name spec)))
      (let [spec+ (extend-spec (get-spec! (:name spec)) spec)]
        `(do ~(registering-form spec+)
             ~(protocol-extension-form spec+))))

    (defn cleaning-form [{:as s :keys [pname mname name arities]}]
      (let [arified-names
            (mapcat (fn [n] [(arify-name mname n) (arify-name pname n)])
                    arities)]
        `(do
           ~@(mapv (fn [x#] `(ns-unmap '~(symbol (str *ns*)) '~x#))
                   (cons name arified-names)))))

    (defn declaration-form [spec]
      #_(println p/*cljs*)
      `(do ~(cleaning-form spec)
           ~(registering-form spec)
           ~(protocol-declaration-form spec)
           ~(function-definition-form spec)
           ~(protocol-extension-form spec)
           ~(:name spec)))

    )

(do :refresh

    (defn implementers
      "given a generic spec,
       returns a vector of all types that implement the corresponding generic"
      [spec]
      (->> (:cases spec)
           (map (fn [[_ & xs]]
                  (reduce (fn [a e]
                            (if (set? e) (into a e) (conj a e)))
                          #{} (map first (partition 2 xs)))))
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
        (compiled-generic-spec name cases)))

    (p/defmac generic+
      "add new cases to an existant generic
       all given arities must already be known"
      [name & cases]
      (extension-form
        (compiled-generic-spec name cases)))

    (p/defmac fork
      "create a new generic from an existing one
       does not alter the original"
      [parent-name name & cases]
      (let [names (derive-name name)
            parent-spec (get-spec! parent-name)
            base-spec (merge parent-spec names)
            extension-spec (compiled-generic-spec name cases)
            spec (extend-spec base-spec extension-spec)]
        (declaration-form spec)))

    (p/defmac implements?
      "test if something implements a generic"
      [name v]
      (let [gspec (get-spec! name)
            proto-prefix (:pname gspec)
            proto-syms (map (partial p/sym (:ns gspec) "/" proto-prefix '_)
                            (map str (:arities gspec)))]
        `(or ~@(mapv (fn [s] `(satisfies? ~s ~v)) proto-syms))))

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
          (let [{:as spec :keys [mname pname]}
                (get-spec! name)
                with-clean-pattern
                (fn [x] (update x :pattern (comp vec (partial remove #{'&}))))
                with-variadic-flag
                (fn [x] (assoc x :variadic (variadic-argv? (:pattern x))))
                with-names
                (fn [x]
                  (let [ari (count (:pattern x))]
                    (assoc x :arity ari
                             :mname (arify-name mname ari)
                             :pname (arify-name pname ari))))]

            (->> (normalize-fn-cases cases)
                 (map (fn [[pat bod]] {:pattern pat :body bod}))
                 (map with-variadic-flag)
                 (map with-clean-pattern)
                 (map with-names))))

        (defn thing_cases->decls [xs]
          (mapcat (fn [{:keys [mname pname body pattern]}]
                    [pname (list mname pattern body)])
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
              (def ~(symbol tag) ~(p/sym "->" class-sym))
              (tag+ ~spec))))
      ([tag fields]
       `(deft ~tag ~fields []))
      ([tag fields parents & impls]
       `(deft ~{:tag tag :parents parents :impls (vec impls) :fields fields}))))

(comment

  (get-reg)
  (tag+ :iop.fop [:vec :set] [:hash])

  (do :implements?-test
      (generic gg1 [x y] :vec [:gg1-vec x y])
      (get-spec! 'gg1)
      (implements? gg1 1)
      (implements? gg1 []))

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




(comment :resolution-xp

    (defn resolve-deep [x env]
      (clojure.walk/prewalk
        (fn [x] (if (symbol? x) (resolve env x) x))
        x))

    (def compiled-generic-spec [name body env]
      (let [spec (generic-spec name body)
            spec (update spec :cases resolve-deep)]))

    (cljs.analyzer/res)
    (clojure.walk/macroexpand-all
      '(let [z 1 a (fn [x] (let [y x] (+ x y z)))]
         (fn [i] (+ i (a i))))))