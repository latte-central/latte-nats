(ns latte-nats.ord
  "The oredering relation for natural numbers."

  (:refer-clojure :exclude [and or not = + < <= > >= int])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]

            [latte-sets.set :as s :refer [elem]]

            [latte-nats.core :as nats :refer [nat = zero succ]]
            [latte-nats.rec :as rec]
            [latte-nats.natint :as natint :refer [nat->natset natset->nat]]
            [latte-nats.plus :as plus :refer [+]]

            [latte-integers.int :as int :refer [int]]
            [latte-integers.nat :as intnat]
            [latte-integers.ord :as iord]
            [latte-integers.plus :as ip]
            [latte-integers.minus :as im]
            ))

(definition <=
  "The lower-or-equal order for natural numbers."
  [[m nat] [n nat]]
  (exists [k nat] (= (+ m k) n)))

(defthm le-refl
  [[n nat]]
  (<= n n))

(proof 'le-refl
  (have <a> (= (+ n zero) n)
        :by (plus/plus-zero n))
  (qed ((q/ex-intro (lambda [k nat] (= (+ n k) n)) zero) <a>)))

(defthm le-trans
  [[m nat] [n nat] [p nat]]
  (==> (<= m n)
       (<= n p)
       (<= m p)))

(proof 'le-trans
  (assume [H1 _
           H2 _]
    (assume [k1 nat
             Hk1 (= (+ m k1) n)]
      (assume [k2 nat
               Hk2 (= (+ n k2) p)]
        (have <a> (= (+ (+ m k1) k2) p)
              :by (eq/rewrite Hk2 (eq/eq-sym Hk1)))
        (have <b> (= (+ m (+ k1 k2)) p)
              :by (eq/rewrite <a> (eq/eq-sym (plus/plus-assoc m k1 k2))))
        (have <c> (<= m p) :by ((q/ex-intro (lambda [k nat] (= (+ m k) p)) (+ k1 k2)) <b>)))
      (have <d> (<= m p) :by (q/ex-elim H2 <c>)))
    (have <e> (<= m p) :by (q/ex-elim H1 <d>)))
  (qed <e>))

(defthm le-antisym
  [[m nat] [n nat]]
  (==> (<= m n)
       (<= n m)
       (= m n)))

(proof 'le-antisym
  (assume [H1 _
           H2 _]
    (assume [k1 nat
             Hk1 (= (+ m k1) n)]
      (assume [k2 nat
               Hk2 (= (+ n k2) m)]
        (have <a> (= (+ (+ m k1) k2) m)
              :by (eq/rewrite Hk2 (eq/eq-sym Hk1)))
        (have <b> (= (+ m (+ k1 k2)) m)
              :by (eq/rewrite <a> (eq/eq-sym (plus/plus-assoc m k1 k2))))
        (have <c> (= (+ k1 k2) zero)
              :by ((plus/plus-refl-zero m (+ k1 k2)) <b>))
        (have <d> (= k1 zero) :by ((plus/plus-any-zero-left k1 k2) <c>))
        (have <e> (= k2 zero) :by ((plus/plus-any-zero-right k1 k2) <c>))
        (have <f> (= (+ n zero) m) :by (eq/rewrite Hk2 <e>))
        (have <g> (= n m) :by (eq/rewrite <f> (plus/plus-zero n))))
      (have <h> (= n m) :by (q/ex-elim H2 <g>)))
    (have <i> (= m n) :by (eq/eq-sym (q/ex-elim H1 <h>))))
  (qed <i>))


(defthm intleq-leq
  [[m nat] [n nat]]
  (==> (iord/<= (nat->natset m)
                (nat->natset n))
       (<= m n)))

(try-proof 'intleq-leq
  (assume [H _]
    (have <a> (exists [k int]
                (and (elem k intnat/nat)
                     (int/= (ip/+ (nat->natset m) k)
                            (nat->natset n))))
          :by ((iord/plus-le-prop (nat->natset m) (nat->natset n)) H))
    (assume [k int
             Hk (and (elem k intnat/nat)
                     (int/= (ip/+ (nat->natset m) k)
                            (nat->natset n)))]

      (have <b1> (int/= k (nat->natset (natset->nat k)))
            :by (eq/eq-sym (natint/nat-natset-inv k (p/and-elim-left Hk))))

      (have <b2> (int/= (ip/+ (nat->natset m) k)
                        (ip/+ (nat->natset m) (nat->natset (natset->nat k))))
            :by (eq/eq-cong (lambda [j int]
                           (ip/+ (nat->natset m) j)) <b1>))

      (have <b3> (int/= (ip/+ (nat->natset m) (nat->natset (natset->nat k)))
                        (nat->natset (+ m (natset->nat k))))
            :by (plus/intplus-plus m (natset->nat k)))

      (have <b4> (int/= (nat->natset (+ m (natset->nat k)))
                        (nat->natset n))
            :by (eq/eq-trans* (eq/eq-sym <b3>) (eq/eq-sym <b2>) (p/and-elim-right Hk)))
      
      (have <b5> (= (+ m (natset->nat k)) n)
            :by ((natint/nat-natset-injective (+ m (natset->nat k)) n) <b4>))
      (have <b> (exists [u nat] (= (+ m u) n))
            :by ((q/ex-intro (lambda [u nat]
                               (= (+ m u) n)) (natset->nat k)) <b5>)))
    (have <c> _ :by (q/ex-elim <a> <b>)))

  (qed <c>))


(definition <
  "The strict variant of [[<=]]."
  [[n nat] [m nat]]
  (and (<= n m)
       (not (= n m))))

(defthm lt-asym
  [[n nat] [m nat]]
  (==> (< n m)
       (not (< m n))))

(proof 'lt-asym
  (assume [Hnm (< n m)]
    (assume [Hmn (< m n)]
      (have <a> (= n m)
            :by ((le-antisym n m)
                 (p/and-elim-left Hnm)
                 (p/and-elim-left Hmn)))
      (have <b> p/absurd :by ((p/and-elim-right Hnm) <a>))))
  (qed <b>))


(defthm lt-trans
  [[n nat] [m nat] [p nat]]
  (==> (< n m)
       (< m p)
       (< n p)))

(proof 'lt-trans
  (assume [Hnm (< n m)
           Hmp (< m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= m p) :by (p/and-elim-left Hmp))
    (have <d> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <e> (<= n p) :by ((le-trans n m p) <a> <c>))
    (assume [Hcut (= n p)]
      (have <f1> (< p m)
            :by (eq/rewrite Hnm Hcut))
      (have <f2> (not (< p m)) :by ((lt-asym m p) Hmp))
      (have <f> p/absurd :by (<f2> <f1>)))
    (have <g> (< n p)
          :by (p/and-intro <e> <f>)))
  (qed <g>))

(defthm lt-trans-weak
  [[n nat] [m nat] [p nat]]
  (==> (<= n m)
       (< m p)
       (< n p)))

(proof 'lt-trans-weak
  (assume [Hnm (<= n m)
           Hmp (< m p)]
    (have <a> (<= m p) :by (p/and-elim-left Hmp))
    (have <b> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <c> (<= n p) :by ((le-trans n m p) Hnm <a>))
    (assume [H (= n p)]
      (have <d1> (<= p m) :by (eq/rewrite Hnm H))
      (have <d2> (= m p) :by ((le-antisym m p) <a> <d1>))
      (have <d> p/absurd :by (<b> <d2>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-trans-weak-alt
  "An alternative to [[lt-trans-weak]]."
  [[n nat] [m nat] [p nat]]
  (==> (< n m)
       (<= m p)
       (< n p)))

(proof 'lt-trans-weak-alt
  (assume [Hnm (< n m)
           Hmp (<= m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= n p) :by ((le-trans n m p) <a> Hmp))
    (assume [H (= n p)]
      (have <d1> (= p n) :by (eq/eq-sym H))
      (have <d2> (<= m n) :by (eq/rewrite Hmp <d1>))
      (have <d3> (= n m) :by ((le-antisym n m) <a> <d2>))
      (have <d> p/absurd :by (<b> <d3>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-le
  [[m nat] [n nat]]
  (==> (< m n)
       (<= m n)))

(proof 'lt-le
  (assume [Hmn (< m n)]
    (have <a> (<= m n)
          :by (p/and-elim-left Hmn)))
  (qed <a>))

(defthm plus-le
  [[m nat] [n nat] [p nat]]
  (==> (<= (+ m p) (+ n p))
       (<= m n)))

(proof 'plus-le
  (assume [H _]
    (assume [k nat
             Hk (= (+ (+ m p) k) (+ n p))]
      
      (have <a> (= (+ (+ m p) k)
                   (+ m (+ p k)))
            :by (eq/eq-sym (plus/plus-assoc m p k)))
      (have <b> (= (+ m (+ p k))
                   (+ m (+ k p)))
            :by (eq/eq-cong (lambda [$ nat]
                              (+ m $)) (plus/plus-commute p k)))
      (have <c> (= (+ m (+ k p))
                   (+ (+ m k) p))
            :by (plus/plus-assoc m k p))
      
      (have <d> (= (+ (+ m p) k) (+ (+ m k) p))
            :by (eq/eq-trans* <a> <b> <c>))

      (have <e> (= (+ (+ m k) p) (+ n p))
            :by (eq/rewrite Hk <d>))

      (have <f> (= (+ m k) n)
            :by ((plus/plus-right-cancel (+ m k) n p) <e>))
      
      (have <g> (exists [k nat] (= (+ m k) n))
            :by ((q/ex-intro (lambda [$ nat] (= (+ m $) n)) k) <f>)))

    (have <h> (<= m n) :by (q/ex-elim H <g>)))

  (qed <h>))

(defthm plus-le-conv
  "The converse of [[plus-le]]."
  [[m nat] [n nat] [p nat]]
  (==> (<= m n)
       (<= (+ m p) (+ n p))))

(proof 'plus-le-conv
  (assume [H _]
    (assume [k nat
             Hk (= (+ m k) n)]
      (have <a> (= (+ (+ m k) p) (+ n p))
            :by (eq/eq-cong (lambda [$ nat]
                              (+ $ p)) Hk))
      (have <b> (= (+ (+ m k) p)
                   (+ (+ m p) k))
            :by (plus/plus-comm-assoc m k p))
      (have <c> (= (+ (+ m p) k) (+ n p))
            :by (eq/rewrite <a> <b>))
      (have <d> (<= (+ m p) (+ n p))
            :by ((q/ex-intro (lambda [k nat] (= (+ (+ m p) k) (+ n p))) k) <c>)))
    (have <e> _ :by (q/ex-elim H <d>)))
(qed <e>))






