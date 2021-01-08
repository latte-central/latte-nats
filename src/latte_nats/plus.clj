(ns latte-nats.plus
  "The addition defined on ℕ."

  (:refer-clojure :exclude [and or not int = +])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]

            [latte-sets.quant :as sq :refer [forall-in]]
            
            [latte-nats.core :as nats :refer [nat = zero succ]]
            [latte-nats.rec :as rec]
            [latte-nats.natint :as natint :refer [nat->natset]]

            [latte-integers.int :as int :refer [int]]
            [latte-integers.plus :as ip]

            ))


(definition add-prop
  "The property of the addition of `m` to an natural integer."
  [[m nat]]
  (lambda [g (==> nat nat)]
    (and (= (g zero) m)
         (forall [n nat]
           (= (g (succ n)) (succ (g n)))))))

(defthm add-unique
  "The unicity of the addition function, through [[add-prop]]."
  [[m nat]]
  (q/unique (add-prop m)))

(proof 'add-unique
  (qed (rec/nat-recur m succ)))

(definition plus
  "The function that adds `m` to a natural integer"
  [[m nat]]
  (q/the (add-unique m)))

(definition +
  "The function that adds `m` to `n`."
  [[m nat] [n nat]]
  ((plus m) n))

(defthm plus-prop
  [[m nat]]
  (and (= ((plus m) zero) m)
       (forall [n nat]
         (= ((plus m) (succ n))
            (succ ((plus m) n))))))

(proof 'plus-prop
  (qed (q/the-prop (add-unique m))))

(defthm plus-zero
  [[m nat]]
  (= (+ m zero) m))

(proof 'plus-zero
  (qed (p/and-elim-left (plus-prop m))))

(defthm plus-succ
  [[m nat] [n nat]]
  (= (+ m (succ n))
     (succ (+ m n))))

(proof 'plus-succ
  (qed ((p/and-elim-right (plus-prop m)) n)))


;; make the basic definitions opaque
;; (otherwise terms become extra-large)
(u/set-opacity! #'plus-prop true)
(u/set-opacity! #'plus true)
(u/set-opacity! #'+ true)

(defthm plus-succ-sym
  [[m nat] [n nat]]
  (= (succ (+ m n))
     (+ m (succ n))))

(proof 'plus-succ-sym
  (qed (eq/eq-sym (plus-succ m n))))

(defthm plus-zero-swap
  [[m nat]]
  (= (+ zero m) m))

(proof 'plus-zero-swap
  "We proceed by induction on `m`."
  "First the case for m=0"
  (have <a> (= (+ zero zero) zero)
        :by (plus-zero zero))
  "Then the inductive case, we assume `(P m)` for some `m`."
  (assume [m nat
           Hind (= (+ zero m) m)]
    "We must show `(P (succ m))`."
    (have <b1> (= (+ zero (succ m))
                  (succ (+ zero m)))
          :by (plus-succ zero m))
    (have <b> (= (+ zero (succ m))
                 (succ m))
          :by (eq/eq-subst (lambda [k nat]
                                   (= (+ zero (succ m))
                                      (succ k)))
                           Hind <b1>)))
  (qed (((nats/nat-induct (lambda [m nat]
                           (= (+ zero m) m)))
        <a> <b>) m)))

(defthm plus-succ-swap
  [[m nat] [n nat]]
  (= (+ (succ m) n)
     (succ (+ m n))))

(proof 'plus-succ-swap
  (have <a1> (= (+ (succ m) zero)
                (succ m))
        :by (plus-zero (succ m)))
  (have <a2> (= (succ m)
                (succ (+ m zero)))
        :by (eq/eq-cong succ (eq/eq-sym (plus-zero m))))
  (have <a> (= (+ (succ m) zero)
               (succ (+ m zero)))
        :by (eq/eq-trans <a1> <a2>))
  (assume [n nat
           Hind (= (+ (succ m) n)
                   (succ (+ m n)))]
    "We show `P (succ n)`."
    (have <b1> (= (+ (succ m) (succ n))
                  (succ (+ (succ m) n)))
          :by (plus-succ (succ m) n))
    (have <b2> (= (succ (+ (succ m) n))
                  (succ (succ (+ m n))))
          :by (eq/eq-cong succ Hind))
    (have <b3> (= (+ (succ m) (succ n))
                  (succ (succ (+ m n))))
          :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (succ (+ m n)))
                  (succ (+ m (succ n))))
          :by (eq/eq-cong succ (eq/eq-sym (plus-succ m n))))
    (have <b> (= (+ (succ m) (succ n))
                 (succ (+ m (succ n))))
          :by (eq/eq-trans <b3> <b4>)))

  (qed (((nats/nat-induct (lambda [n nat]
                            (= (+ (succ m) n)
                               (succ (+ m n)))))
         <a> <b>) n)))


(defthm plus-commute
  [[n nat] [m nat]]
  (= (+ n m)
     (+ m n)))

(proof 'plus-commute
  "We proceed by induction on `n`."
  (pose P := (lambda [k nat] (= (+ k m) (+ m k))))
  "First let's prove `(P zero)`."
  (have <a1> (= m (+ m zero))
        :by (eq/eq-sym (plus-zero m)))
  (have <a> (P zero) :by (eq/eq-trans (plus-zero-swap m) <a1>))
  "Now the inductive cases."
  (assume [k nat
           Hind (P k)]
    "We show `(P (succ k))`."
    (have <b1> (= (+ (succ k) m)
                  (succ (+ k m)))
          :by (plus-succ-swap k m))
    (have <b2> (= (succ (+ k m))
                  (succ (+ m k)))
          :by (eq/eq-cong succ Hind))
    (have <b3> (= (+ (succ k) m)
                  (succ (+ m k))) :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (+ m k))
                  (+ m (succ k))) :by (eq/eq-sym (plus-succ m k)))
    (have <b> (P (succ k)) :by (eq/eq-trans <b3> <b4>)))

  "Now we apply integer induction."
  (have <e> (P n) :by ((nats/nat-induct P) <a> <b> n))
  (qed <e>))


;; from now on, we will connect to the latte-integers developement,
;; which defines formally the set of natural numbers as a subset
;; of the (signed) integers.

(defthm intplus-plus
  []
  (forall-in [m intnat/nat]
    (forall-in [n intnat/nat]
      (= (natset->nat (ip/+ m n))
         (+ (natset->nat m) (natset->nat n)))))

(defthm plus-assoc
  [[n nat] [m nat] [p nat]]
  (= (+ n (+ m p))
     (+ (+ n m) p)))

(proof 'plus-assoc
  (have <a> (int/= (ip/+ (nat->natset n) (ip/+ (nat->natset m) (nat->natset p)))
                   (ip/+ (ip/+ (nat->natset n) (nat->natset m)) (nat->natset p)))
        :by (ip/plus-assoc (nat->natset n) (nat->natset m) (nat->natset p))))
