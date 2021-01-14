(ns latte-nats.natint
  "Connection between ℕ as a type (this development)
 and ℕ as a subset of ℤ (the latte-integers development)."

  (:refer-clojure :exclude [and or not int = +])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and and* or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            
            [latte-sets.set :as sets :refer [elem]]
            [latte-sets.quant :a sq :refer [forall-in]]
            [latte-sets.quant :a sq :refer [forall-in]]

            [latte-nats.core :as nats :refer [nat = zero succ]]
            [latte-nats.rec :as rec]

            [latte-integers.int :as int :refer [int]]
            [latte-integers.nat :as intnat]
            [latte-integers.rec :as intrec]

            ))


(definition fzero
  [n nat]
  zero)

(definition natset->nat-prop
  []
  (lambda [g (==> int nat)]
    (and (= (g int/zero) zero)
         (forall [n int]
           (and (==> (intnat/positive (int/succ n))
                     (= (g (int/succ n)) (succ (g n))))
                (==> (intnat/negative (int/pred n))
                     (= (g (int/pred n)) (fzero (g n)))))))))

(defthm natset->nat-prop-unique
  []
  (q/unique (natset->nat-prop)))

(proof 'natset->nat-prop-unique
  (qed (intrec/int-recur zero succ fzero)))

(definition natset->nat
  "Conversion from integers to natural numbers,
 Note that all negative numbers map to zero."
  [n int]
  ((q/the (natset->nat-prop-unique)) n))

(defthm natset-nat-zero
  []
  (= (natset->nat int/zero) zero))

(proof 'natset-nat-zero
  (qed (p/and-elim-left (q/the-prop (natset->nat-prop-unique)))))

(defthm natset-nat-succ
  [n int]
  (==> (elem n intnat/nat)
       (= (natset->nat (int/succ n)) (succ (natset->nat n)))))

(proof 'natset-nat-succ
  (assume [Hn _]
    (have <a1> (intnat/positive (int/succ n)) 
          :by ((intnat/positive-succ n) Hn))
    (have <a> (= (natset->nat (int/succ n)) (succ (natset->nat n)))
          :by ((p/and-elim-left ((p/and-elim-right (q/the-prop (natset->nat-prop-unique))) n))
               <a1>)))
  (qed <a>))


(definition nat->natset-prop
  []
  (lambda [g (==> nat int)]
    (and (int/= (g zero) int/zero)
         (forall [n nat]
           (int/= (g (succ n)) (int/succ (g n)))))))

(defthm nat->natset-prop-unique
  []
  (q/unique (nat->natset-prop)))

(proof 'nat->natset-prop-unique
  (qed (rec/nat-recur int/zero int/succ)))

(definition nat->natset
  "Conversion from natural numbers to integers."
  [n nat]
  ((q/the (nat->natset-prop-unique)) n))

(defthm nat-natset-zero
  []
  (int/= (nat->natset zero) int/zero))

(proof 'nat-natset-zero
  (qed (p/and-elim-left (q/the-prop (nat->natset-prop-unique)))))

(defthm nat-natset-succ
  [n nat]
  (int/= (nat->natset (succ n)) (int/succ (nat->natset n))))

(proof 'nat-natset-succ
  (qed ((p/and-elim-right (q/the-prop (nat->natset-prop-unique))) n)))

(defthm nat-in-natset
  []
  (forall [n nat]
    (elem (nat->natset n) intnat/nat)))

(proof 'nat-in-natset
  (pose P := (lambda [k nat] (elem (nat->natset k) intnat/nat)))
  "By induction, case zero"
  (have <a1> (int/= (nat->natset zero) int/zero) :by (nat-natset-zero))
  (have <a2> (elem int/zero intnat/nat) :by (intnat/nat-zero))
  (have <a> (P zero) :by (eq/rewrite <a2> (eq/eq-sym <a1>)))
  "Case succ"
  (assume [n nat
           Hn (P n)]
    "We must prove (P (succ n))"
    (have <b1> (int/= (nat->natset (succ n)) (int/succ (nat->natset n)))
          :by (nat-natset-succ n))
    (have <b2> (elem (int/succ (nat->natset n)) intnat/nat)
          :by ((intnat/nat-succ (nat->natset n))
               Hn))
    (have <b> (P (succ n)) :by (eq/rewrite <b2> (eq/eq-sym <b1>))))
  "Induction principle"
  (have <c> (forall [n nat] (P n))
        :by ((nats/nat-induct P) <a> <b>))
  (qed <c>))

(defthm natset-nat-inv 
  "Conversion from and to natural numbers."
  []
  (forall [n nat]
    (= (natset->nat (nat->natset n)) n)))

(proof 'natset-nat-inv
  (pose P := (lambda [k nat] (= (natset->nat (nat->natset k)) k)))
  "By inducion, case zero"
  (have <a1> (int/= (nat->natset zero) int/zero)
        :by (nat-natset-zero))
  (have <a2> (= (natset->nat int/zero) zero)
        :by (natset-nat-zero))
  (have <a> (P zero) :by (eq/rewrite <a2> (eq/eq-sym <a1>)))
  "Case succ"
  (assume [n nat
           Hn (P n)]
    "We must prove (P (succ n))"
    (have <b1> (int/= (nat->natset (succ n)) (int/succ (nat->natset n)))
          :by (nat-natset-succ n))

    (have <b2> (elem (nat->natset n) intnat/nat)
          :by ((nat-in-natset) n))

    (have <b3> (= (natset->nat (int/succ (nat->natset n))) (succ (natset->nat (nat->natset n))))
          :by ((natset-nat-succ (nat->natset n)) <b2>))

    (have <b4> (= (natset->nat (int/succ (nat->natset n))) (succ n))
          :by (eq/rewrite <b3> Hn))

    (have <b> (P (succ n)) 
          :by (eq/rewrite <b4> (eq/eq-sym <b1>))))
  "Inductive principle"
  (have <c> (forall [n nat] (P n)) :by ((nats/nat-induct P) <a> <b>))
  (qed <c>))


(defthm nat-natset-inv 
  "Conversion to and from natural numbers."
  []
  (forall-in [n intnat/nat]
    (int/= (nat->natset (natset->nat n)) n)))

(proof 'nat-natset-inv
  "We will use the induction principle from nats/nat-induct."
  (pose P := (lambda [k int] (int/= (nat->natset (natset->nat k)) k)))
  "Case zero"
  (have <a1> (= (natset->nat int/zero) zero) :by (natset-nat-zero))
  (have <a2> (int/= (nat->natset zero) int/zero) :by (nat-natset-zero))
  (have <a> (P int/zero) :by (eq/rewrite <a2> (eq/eq-sym <a1>)))
  "Case succ"
  (assume [n int
           Hn (elem n intnat/nat)
           Hrec (P n)]
    "We have to proove (P (int/succ n))"
    (have <b1> (= (natset->nat (int/succ n)) (succ (natset->nat n)))
          :by ((natset-nat-succ n) Hn))
    (have <b2> (int/= (nat->natset (natset->nat (int/succ n)))
                  (nat->natset (succ (natset->nat n))))
          :by (eq/eq-cong nat->natset <b1>))
    (have <b3> (int/= (nat->natset (succ (natset->nat n)))
                      (int/succ (nat->natset (natset->nat n))))
          :by (nat-natset-succ (natset->nat n)))
    (have <b4> (int/= (nat->natset (natset->nat (int/succ n)))
                      (int/succ (nat->natset (natset->nat n))))
          :by (eq/rewrite <b2> <b3>))
    (have <b> (P (int/succ n)) 
          :by (eq/rewrite <b4> Hrec)))
  "Induction principle"
  (have <c> (forall-in [n intnat/nat] (P n))
        :by ((intnat/nat-induct P) <a> <b>))
  (qed <c>))


(defthm int-to-nat
  "Any property `P` of positive integers is also a property
of natural numbers."
  [P (==> nat :type)]
  (==> (forall [n int] (P (natset->nat n)))
       (forall [n nat] (P n))))

(proof 'int-to-nat
  (assume [H _]
    "By case analysis, case zero"
    (have <a1> (P (natset->nat int/zero))
          :by (H int/zero))
    (have <a2> (= (natset->nat int/zero) zero)
          :by (natset-nat-zero))
    (have <a> (P zero) :by (eq/rewrite <a1> <a2>))
    "Case succ"
    (assume [n nat]
      "We have to proove (P (succ n))"
      (have <b1> (P (natset->nat (int/succ (nat->natset n)))) 
            :by (H (int/succ (nat->natset n))))
      (have <b2> (= (natset->nat (int/succ (nat->natset n)))
                    (succ (natset->nat (nat->natset n))))
      :by ((natset-nat-succ (nat->natset n)) (nat-in-natset n)))
      (have <b3> (= (natset->nat (int/succ (nat->natset n)))
                    (succ n))
            :by (eq/rewrite <b2> (natset-nat-inv n)))
      (have <b> (P (succ n))
            :by (eq/rewrite <b1> <b3>)))
    "Induction principle"
    (have <c> (forall [n nat] (P n))
          :by ((nats/nat-case P) <a> <b>)))
  (qed <c>))

;;; TODO : the converse  nat-to-int  (but it's less useful because
;;; the objective is mostly to port proofs for the integer developments,
;;; but it could be useful to populate natset later on...)


(defthm nat-natset-injective
  "The conversion to integers is injective."
  [[m n nat]]
  (==> (int/= (nat->natset m) (nat->natset n))
       (= m n)))

(proof 'nat-natset-injective
  (assume [Heq _]
    (have <a> (= (natset->nat (nat->natset m))
                 (natset->nat (nat->natset n)))
          :by (eq/eq-cong natset->nat Heq))
    (have <b> (= (natset->nat (nat->natset m))
                 m)
          :by (natset-nat-inv m))
    (have <c> _ :by (eq/eq-trans (eq/eq-sym <b>) <a>))
    (have <d> (= (natset->nat (nat->natset n))
                 n)
          :by (natset-nat-inv n))
    (have <e> (= m n) :by (eq/eq-trans <c> <d>)))
  (qed <e>))

;;; TODO : natset-nat-injective  (but less needed in the nat development)

(definition natset-fun
  "Conversion of a function `f` on integers to a function on natural numbers."
  [f (==> int int)]
  (lambda [n nat]
    (natset->nat (f (nat->natset n)))))

(definition natset-prop
  "Convertion of a property `P` on integers to a property on natural numbers."
  [P (==> int :type)]
  (lambda [n nat]
    (P (nat->natset n))))

(definition natset-fun2
  "Conversion of a binary function `f` on integers to a function on natural numbers."
  [f (==> int int int)]
  (lambda [m n nat]
    (natset->nat (f (nat->natset m) (nat->natset n)))))

(u/set-opacity! #'natset->nat true)
(u/set-opacity! #'nat->natset true)
