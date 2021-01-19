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
       (= n m)))

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
    (have <i> (= n m) :by (q/ex-elim H1 <h>)))
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


