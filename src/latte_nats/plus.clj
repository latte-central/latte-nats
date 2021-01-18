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
            [latte-nats.natint :as natint :refer [nat->natset natset->nat]]

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
          :by (eq/rewrite <b1> Hind)))
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
  (forall [m n nat]
    (int/= (ip/+ (nat->natset m) 
                 (nat->natset n))
           (nat->natset (+ m n)))))

(proof 'intplus-plus
  "By induction on n"
  (assume [m nat]
    (pose P := (lambda [k nat] (int/= (ip/+ (nat->natset m)
                                            (nat->natset k))
                                      (nat->natset (+ m k)))))
    "Case zero"
    (have <a1> (int/= (nat->natset zero) int/zero)
          :by (natint/nat-natset-zero))
    (have <a2> (int/= (ip/+ (nat->natset m)
                            (nat->natset zero))
                      (ip/+ (nat->natset m) int/zero))
          :by (eq/nrewrite 2 (eq/eq-refl (ip/+ (nat->natset m) (nat->natset zero))) <a1>))
    (have <a3> (int/= (ip/+ (nat->natset m) int/zero)
                      (nat->natset m))
          :by (ip/plus-zero (nat->natset m)))
    (have <a4> (= m (+ m zero)) :by (eq/eq-sym (plus-zero m)))
    (have <a5> (int/= (nat->natset m)
                      (nat->natset (+ m zero)))
          :by (eq/nrewrite 2 (eq/eq-refl (nat->natset m)) <a4>))
    (have <a> (P zero)
          :by (eq/eq-trans* <a2> <a3> <a5>))
    "Case succ"
    (assume [n nat
             Hn (P n)]
      "We must prove (P (succ n))"
      "First, a certain number of equalities ..."
      (have <b1> (int/= (nat->natset (succ n))
                        (int/succ (nat->natset n)))
            :by (natint/nat-natset-succ n))
      (have <b2> (int/= (ip/+ (nat->natset m) (int/succ (nat->natset n)))
                        (int/succ (ip/+ (nat->natset m) (nat->natset n))))
            :by (ip/plus-succ (nat->natset m) (nat->natset n)))
      (have <b3> (int/= (ip/+ (nat->natset m) (nat->natset n))
                        (nat->natset (+ m n)))
            :by Hn)
      (have <b4> (int/= (int/succ (nat->natset (+ m n)))
                        (nat->natset (succ (+ m n))))
            :by (eq/eq-sym (natint/nat-natset-succ (+ m n))))
      (have <b5> (= (succ (+ m n)) (+ m (succ n)))
            :by (eq/eq-sym (plus-succ m n)))
      "And now, we reconstruct our goal."
      (have <c1> (int/= (ip/+ (nat->natset m) (nat->natset (succ n)))
                        (int/succ (ip/+ (nat->natset m) (nat->natset n))))
            :by (eq/rewrite <b2>  (eq/eq-sym <b1>)))
      (have <c2> (int/= (int/succ (ip/+ (nat->natset m) (nat->natset n)))
                        (int/succ (nat->natset (+ m n))))
            :by (eq/eq-cong int/succ <b3>))
      (have <c3> (int/= (int/succ (nat->natset (+ m n)))
                        (nat->natset (+ m (succ n))))
            :by (eq/rewrite <b4> <b5>))
      (have <c> (P (succ n))
            :by (eq/eq-trans* <c1> <c2> <c3>)))
    "Induction principle"
    (have <d> _ ;;; XXX : (forall [n nat] (P n)) 
                ;;; instead of underscore does not work (but should ?)
          :by ((nats/nat-induct P) <a> <c>)))
  (qed <d>))

(defthm plus-assoc
  [[n nat] [m nat] [p nat]]
  (= (+ n (+ m p))
     (+ (+ n m) p)))

;;; XXX: may the following be done in a simpler way  (i.e. reusing results from
;;; the integer development)
(proof 'plus-assoc
  (have <a> (int/= (ip/+ (nat->natset n) (ip/+ (nat->natset m) (nat->natset p)))
                   (ip/+ (ip/+ (nat->natset n) (nat->natset m)) (nat->natset p)))
        :by (ip/plus-assoc (nat->natset n) (nat->natset m) (nat->natset p)))
  "We handle the first operand of equality"
  (have <b1> (int/= (ip/+ (nat->natset n) (ip/+ (nat->natset m) (nat->natset p)))
                    (ip/+ (nat->natset n) (nat->natset (+ m p))))
        :by (eq/eq-cong (lambda [$ int]
                           (ip/+ (nat->natset n) $))
                        (intplus-plus m p)))
  (have <b2> (int/= (ip/+ (nat->natset n) (nat->natset (+ m p)))
                    (nat->natset (+ n (+ m p))))
        :by (intplus-plus n (+ m p)))
  (have <b3> _ :by (eq/eq-trans <b1> <b2>))
  (have <b> (int/= (nat->natset (+ n (+ m p)))
                   (ip/+ (ip/+ (nat->natset n) (nat->natset m)) (nat->natset p)))
        :by (eq/rewrite <a> <b3>))

  "And now the second operand"
  (have <c1> (int/= (ip/+ (ip/+ (nat->natset n) (nat->natset m)) (nat->natset p))
                    (ip/+ (nat->natset (+ n m)) (nat->natset p)))
        :by (eq/eq-cong (lambda [$ int]
                          (ip/+ $ (nat->natset p)))
                        (intplus-plus n m)))
  (have <c2> (int/= (ip/+ (nat->natset (+ n m)) (nat->natset p))
                   (nat->natset (+ (+ n m) p)))
        :by (intplus-plus (+ n m) p))
  (have <c3> _ :by (eq/eq-trans <c1> <c2>))

  "And we join the two parts"
  (have <d> (int/= (nat->natset (+ n (+ m p)))
                   (nat->natset (+ (+ n m) p)))
        :by (eq/eq-trans <b> <c3>))
  "And finally, we conclude thanks to injectivity"
  (qed ((natint/nat-natset-injective (+ n (+ m p)) (+ (+ n m) p))
        <d>)))

(defthm plus-right-cancel
  [[n nat] [m nat] [p nat]]
  (==> (= (+ n p) (+ m p))
       (= n m)))

(proof 'plus-right-cancel
  (assume [H _]
    (have <a> (int/= (nat->natset (+ n p))
                     (ip/+ (nat->natset n)
                           (nat->natset p)))
          :by (eq/eq-sym (intplus-plus n p)))
    (have <b> (int/= (nat->natset (+ m p))
                     (ip/+ (nat->natset m)
                           (nat->natset p)))
          :by (eq/eq-sym (intplus-plus m p)))
    (have <c> (int/= (nat->natset (+ n p))
                     (nat->natset (+ m p)))
          :by (eq/eq-cong nat->natset H))
    (have <d> _ :by (eq/eq-trans* (eq/eq-sym <a>) <c> <b>))
    (have <e> (int/= (nat->natset n) (nat->natset m))
          :by ((ip/plus-right-cancel (nat->natset n) (nat->natset m) (nat->natset p))
               <d>))
    (have <f> (= n m) :by ((natint/nat-natset-injective n m) <e>)))
  (qed <f>))

(defthm plus-left-cancel
  [[n nat] [m nat] [p nat]]
  (==>  (= (+ p n) (+ p m))
        (= n m)))

(proof 'plus-left-cancel
  (assume [H (= (+ p n) (+ p m))]
    (have <a> (= (+ n p) (+ p m))
          :by (eq/rewrite H (plus-commute p n)))
    (have <b> (= (+ n p) (+ m p))
          :by (eq/rewrite <a> (plus-commute p m)))
    (have <c> (= n m) :by ((plus-right-cancel n m p) <b>)))
  (qed <c>))

(defthm plus-right-cancel-conv
  [[n nat] [m nat] [p nat]]
  (==> (= n m)
       (= (+ n p) (+ m p))))

(proof 'plus-right-cancel-conv
  (assume [H (= n m)]
    (have <a> (= (+ n p) (+ m p))
          :by (eq/eq-cong (lambda [k nat] (+ k p))
                          H)))
  (qed <a>))

(defthm plus-left-cancel-conv
  [[n nat] [m nat] [p nat]]
  (==> (= n m)
       (= (+ p n) (+ p m))))

(proof 'plus-left-cancel-conv
  (assume [H (= n m)]
    (have <a> (= (+ p n) (+ p m))
          :by (eq/eq-cong (lambda [k nat] (+ p k))
                          H)))
  (qed <a>))


(defthm plus-refl-zero
  [[n nat] [k nat]]
  (==> (= (+ n k) n)
       (= k zero)))

(proof 'plus-refl-zero
  (assume [H _]
    (have <a> (= n (+ n zero))
          :by (eq/eq-sym (plus-zero n)))
    (have <b> (= (+ n k) (+ n zero))
          :by (eq/nrewrite 2 H <a>))
    (have <c> (= k zero)
          :by ((plus-left-cancel k zero n) <b>)))
  (qed <c>))


(defthm plus-any-zero-left
  [[m nat] [n nat]]
  (==> (= (+ m n) zero)
       (= m zero)))

(proof 'plus-any-zero-left
  (pose P := (lambda [k nat] (==> (= (+ m k) zero)
                                  (= m zero))))
  "By case analysis"
  "Case zero"
  (assume [Hz (= (+ m zero) zero)]
    (have <a1> (= (+ m zero) m)
          :by (plus-zero m))
    (have <a2> (= m zero) :by (eq/rewrite Hz <a1>)))
  (have <a> (P zero) :by <a2>)

  "Case succ"
  (assume [k nat]
    (assume [Hsucc (= (+ m (succ k)) zero)]
      (have <b1> (= (succ (+ m k)) zero)
            :by (eq/rewrite Hsucc (plus-succ m k)))
      (have <b2> p/absurd :by ((nats/zero-not-succ (+ m k)) <b1>))
      (have <b3> (= m zero) :by (<b2> (= m zero))))
    (have <b> (P (succ k)) :by <b3>))

  (have <c> (forall [k nat] (P k)) :by ((nats/nat-case P) <a> <b>))
 
(qed (<c> n)))
    
    
(defthm plus-any-zero-right
  [[m nat] [n nat]]
  (==> (= (+ m n) zero)
       (= n zero)))

(proof 'plus-any-zero-right
  (have <a> (==> (= (+ n m) zero)
                 (= n zero))
        :by (plus-any-zero-left n m))
  (have <b> (= (+ n m) (+ m n))
        :by (plus-commute n m))
  (qed (eq/rewrite <a> <b>)))



