(ns meander.strategy.epmacro
  "Rewrite strategy combinators.

  A strategy is a unary function of a term (any object) and returns
  the term rewritten.

  Notation:

  t ∈ Term
  p, q, r, s ∈ Strategy"
  (:refer-clojure :exclude [find while repeat some spread])
  #?(:cljs (:require-macros [meander.strategy.epsilon]))
  (:require
   [clojure.core :as clj]
   [clojure.set :as set]
   [clojure.spec.alpha :as s]
   [meander.match.epsilon :as r.match :include-macros true]
   [meander.match.syntax.epsilon :as r.match.syntax :include-macros true]
   [meander.protocols.epsilon :as r.protocols]
   [meander.substitute.epsilon :as r.substitute :include-macros true]
   [meander.syntax.epsilon :as r.syntax :include-macros true]))





(defmacro pipe-body
  {:private true}
  ([params]
   (let [t (gensym "t__")]
     `(if (or ~@(map (partial list `fail?) params))
        *fail*
        (fn [~t]
          ~(reduce
            (fn [inner-form p]
              `(let [~t (~p ~t)]
                 (if (fail? ~t)
                   *fail*
                   ~inner-form)))
            t
            (reverse params)))))))





(defmacro choice-body
  {:private true}
  [params]
  (let [t (gensym "t__")
        t* (gensym "t__")]
    `(fn [~t]
       ~(reduce
         (fn [inner-form p]
           `(let [~t* (~p ~t)]
              (if (fail? ~t*)
                ~inner-form
                ~t*)))
         `*fail*
         (reverse params)))))


(defmacro iseq-all-body
  [t s]
  `(let [res# (reduce
                (fn [t*# x#]
                  (let [x*# (~s x#)]
                    (if (fail? x*#)
                      (reduced *fail*)
                      (concat t*# (list x*#)))))
                ()
                ~t)]
     (if (fail? res#)
       res#
       (vary-meta res# (fn [new-meta#] (merge (meta ~t) new-meta#))))))


(defmacro ivector-all-body
  {:private true}
  [t s]
  `(reduce
    (fn [t*# x#]
      (let [x*# (~s x#)]
        (if (fail? x*#)
          (reduced *fail*)
          (conj t*# x*#))))
    (empty ~t)
    ~t))


(defmacro imap-all-body
  {:private true}
  [t s]
  `(reduce-kv
    (fn [t*# k# v#]
      (let [k*# (~s k#)]
        (if (fail? k*#)
          *fail*
          (let [v*# (~s v#)]
            (if (fail? v*#)
              *fail*
              (assoc t*# k*# v*#))))))
    (empty ~t)
    ~t))


(defmacro irecord-all-body
  {:private true}
  [t s]
  `(reduce-kv
    (fn [t*# k# v#]
      (let [k*# (~s k#)]
        (if (fail? k*#)
          *fail*
          (let [v*# (~s v#)]
            (if (fail? v*#)
              *fail*
              (assoc t*# k*# v*#))))))
    ~t
    ~t))

(defmacro iset-all-body
  {:private true}
  [t s]
  `(reduce
    (fn [t*# x#]
      (let [x*# (~s x#)]
        (if (fail? x*#)
          (reduced *fail*)
          (conj t*# x*#))))
    (empty ~t)
    ~t))



(defmacro iseq-one-body
  {:private true}
  [t s]
  `(reduce
    (fn [_acc# [i# x#]]
      (let [x*# (~s x#)]
        (if (fail? x*#)
          *fail*
          (reduced (concat (take i# ~t)
                           (list x*#)
                           (drop (inc i#) ~t))))))
    *fail*
    (map-indexed vector ~t)))


(defmacro ivector-one-body
  {:private true}
  [t s]
  `(reduce-kv
    (fn [acc# i# x#]
      (let [x*# (~s x#)]
        (if (fail? x*#)
          acc#
          (reduced (assoc ~t i# x*#)))))
    *fail*
    ~t))


(defmacro imap-one-body
  {:private true}
  [t s]
  `(reduce-kv
    (fn [acc# k# v#]
      (let [k*# (~s k#)]
        (if (fail? k*#)
          (let [v*# (~s v#)]
            (if (fail? v*#)
              acc#
              (reduced (assoc ~t k# v*#))))
          (reduced (assoc ~t k*# v#)))))
    *fail*
    ~t))

(defmacro iset-one-body
  {:private true}
  [t s]
  `(reduce
    (fn [acc# x#]
      (let [x*# (~s x#)]
        (if (fail? x*#)
          *fail*
          (reduced (conj (disj ~t x#) x*#)))))
    *fail*
    ~t))



(defmacro iseq-some-body
  {:private true}
  [t s]
  `(let [[t*# pass?#]
         (reduce
          (fn [[t*# pass?#] x#]
            (let [x*# (~s x#)]
              (if (fail? x*#)
                [(cons x# t*#) pass?#]
                [(cons x*# t*#) true])))
          [() false]
          (reverse ~t))]
     (if pass?#
       t*#
       *fail*)))


(defmacro ivector-some-body
  {:private true}
  [t s]
  `(let [[t*# pass?#]
         (reduce-kv
          (fn [[t*# pass?#] i# x#]
            (let [x*# (~s x#)]
              (if (fail? x*#)
                [t*# pass?#]
                [(assoc t*# i# x*#) true])))
          [~t false]
          ~t)]
     (if pass?#
       t*#
       *fail*)))


(defmacro imap-some-body
  {:private true}
  [t s]
  `(let [[t*# pass?#]
         (reduce-kv
          (fn [[t*# pass?#] k# v#]
            (let [k*# (~s k#)
                  v*# (~s v#)]
              (case [(fail? k*#) (fail? v*#)]
                [true true]
                [(assoc t*# k# v#) pass?#]

                [true false]
                [(assoc t*# k# v*#) true]

                [false true]
                [(assoc t*# k*# v#) true]

                [false false]
                [(assoc t*# k*# v*#) true])))
          [{} false]
          ~t)]
     (if pass?#
       t*#
       *fail*)))


(defmacro irecord-some-body
  {:private true}
  [t s]
  `(let [[t*# pass?#]
         (reduce-kv
          (fn [[t*# pass?#] k# v#]
            (let [k*# (~s k#)
                  v*# (~s v#)]
              (case [(fail? k*#) (fail? v*#)]
                [true true]
                [(assoc t*# k# v#) pass?#]

                [true false]
                [(assoc t*# k# v*#) true]

                [false true]
                [(assoc t*# k*# v#) true]

                [false false]
                [(assoc t*# k*# v*#) true])))
          [~t false]
          ~t)]
     (if pass?#
       t*#
       *fail*)))


(defmacro iset-some-body
  {:private true}
  [t s]
  `(let [[t*# pass?#]
         (reduce
          (fn [[t*# pass?#] x#]
            (let [x*# (~s x#)]
              (if (fail? x*#)
                [(conj t*# x#) pass?#]
                [(conj t*# x*#) true])))
          [#{} false]
          ~t)]
     (if pass?#
       t*#
       *fail*)))


(defmacro iseq-retain-body
  {:private true}
  [t s]
  `(sequence (comp (map ~s) (remove fail?)) ~t))


(defmacro ivector-retain-body
  {:private true}
  [t s]
  `(into [] (comp (map ~s) (remove fail?)) ~t))


(defmacro iset-retain-body
  {:private true}
  [t s]
  `(into #{} (comp (map ~s) (remove fail?)) ~t))


(defmacro imap-retain-body
  {:private true}
  [t s]
  `(into {} (comp (map ~s) (remove fail?)) ~t))


(defmacro tuple-body
  {:private true}
  [params]
  (let [t (gensym "t__")
        t*s (mapv gensym (clj/repeat (count params) "t__"))]
    `(fn [~t]
       ~(reduce
         (fn [inner-form [t* param]]
           `(let [~t* (~param ~t)]
              (if (fail? ~t*)
                *fail*
                ~inner-form)))
         t*s
         (reverse (map vector t*s params))))))


(defmacro match
  "Strategy version of match which defaults to returning *fail*."
  {:style/indent 0}
  [& clauses]
  `(fn [x#]
     (r.match/match x#
       ~@clauses

       ~'_
       *fail*)))


(defmacro search
  "Strategy version of search."
  {:style/indent 0}
  [& clauses]
  `(fn [x#]
     (r.match/search x#
       ~@clauses)))


(defmacro find
  "Strategy version of meander.match.epsilon/find that defaults to
  returning *fail*."
  {:style/indent 0}
  [& clauses]
  `(fn [x#]
     (r.match/find x#
       ~@clauses)))


(defmacro rewrite
  "Returns strategy which symbolically transforms `t` in to `t*` via
  pattern matching and substitution. Pattern matching is conducted
  using `find`.

  Example:

  (let [s (rewrite
           (let* [!bs !vs ..1]
             . !body ...)
           (let* [!bs !vs]
             (let* [!bs !vs ...]
               . !body ...)))]
    (s '(let* [b1 :v1, b2 :v2, b3 :v3]
          (vector b1 b2 b3))))
    ;; =>
    (let* [b1 :v1]
      (let* [b2 :v2
             b3 :v3]
        (vector b1 b2 b3)))"
  [& rules]
  `(find
     ~@(mapcat
        (fn [[pat rhs]]
          [pat `(r.substitute/substitute ~rhs)])
        (partition 2 rules))
     ~'_
     *fail*))

(s/fdef rewrite
  :args :meander.match.epsilon.match/clauses
  :ret any?)

(defmacro rewrites
  [& rules]
  `(search
    ~@(mapcat
       (fn [[pat rhs]]
         [pat `(r.substitute/substitute ~rhs)])
       (partition 2 rules))))

