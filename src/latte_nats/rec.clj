(ns latte-nats.rec
  "The recursion theorem for natural numbers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte-prelude.prop :as p :refer [and not]]
            [latte-nats.core :as nats :refer [nat zero succ =]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.classic :as classic]

            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.powerrel :as prel]
            ))

(definition nat-recur-prop
  "The property of the recursion principle for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [g (==> nat T)]
    (and (equal (g zero) x)
         (forall [n nat]
           (equal (g (succ n)) (f (g n)))))))

(defthm nat-recur
  "The recursion principle for natural numbers.
cf. [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (q/unique (nat-recur-prop x f)))


(definition nat-recur-prop-rel
  "A relational variant of the recursion principle [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [R (rel nat T)]
     (and (R zero x)
          (forall [n nat]
            (forall [y T]
              (==> (R n y)
                   (R (succ n) (f y))))))))

(definition nat-fixpoint-rel
  "The relational definition of the least fixed-point
for (primitive) recursive functions on natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rintersections (nat-recur-prop-rel x f)))
;; (lambda [n nat]
;;   (lambda [y T]
;;     (forall [R (rel nat T)]
;;       (==> (prel/rel-elem R (nat-recur-prop-rel x f))
;;            (R n y)))))

(defthm nat-fixpoint-zero
  [[?T :type] [x T] [f (==> T T)]]
  ((nat-fixpoint-rel x f) zero x))

(proof 'nat-fixpoint-zero-thm
  (assume [R (rel nat T)
           HR (prel/rel-elem R (nat-recur-prop-rel x f))]
    (have <a> (R zero x) :by (p/and-elim-left HR)))
  (qed <a>))

(defthm nat-fixpoint-succ
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (forall [y T]
      (==> ((nat-fixpoint-rel x f) n y)
           ((nat-fixpoint-rel x f) (succ n) (f y))))))

(proof 'nat-fixpoint-succ-thm
  (assume [n nat
           y T
           Hny ((nat-fixpoint-rel x f) n y)]
    (assume [R (rel nat T)
             HR (prel/rel-elem R (nat-recur-prop-rel x f))]
      (have <a> (R n y) :by (Hny R HR))
      (have <b> (R (succ n) (f y)) :by ((p/and-elim-right HR) n y <a>))))
  (qed <b>))

(defthm nat-fixpoint-elem
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rel-elem (nat-fixpoint-rel x f) (nat-recur-prop-rel x f)))

(proof 'nat-fixpoint-elem-thm
  (qed (p/and-intro (nat-fixpoint-zero x f)
                    (nat-fixpoint-succ x f))))


(defthm nat-fixpoint-prop
  [[?T :type] [x T] [f (==> T T)]]
  (forall [R (rel nat T)]
        (==> (prel/rel-elem R (nat-recur-prop-rel x f))
             (rel/subrel (nat-fixpoint-rel x f) R))))

(proof 'nat-fixpoint-prop-thm
  (qed (prel/rintersections-lower-bound (nat-recur-prop-rel x f))))


(defthm nat-recur-rel-ex
  "The existential part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (exists [y T] ((nat-fixpoint-rel x f) n y))))


(proof 'nat-recur-rel-ex-thm
  "We proceed by induction on `n`."

  (pose FIX := (nat-fixpoint-rel x f))

  "Base case n=0 : we want to prove (FIX zero y) is true for some y."
  (have <a1> (FIX zero x) :by (nat-fixpoint-zero x f))
  (have <a> (exists [y T] (FIX zero y))
        :by ((q/ex-intro (lambda [y T] (FIX zero y)) x) <a1>))

  "Inductive case"
  (assume [n nat
           Hn (exists [y T] (FIX n y))]
    (assume [y T
             Hy (FIX n y)]
      (have <b1> (FIX (succ n) (f y))
            :by ((nat-fixpoint-succ x f) n y Hy))
      (have <b2> (exists [z T] (FIX (succ n) z))
            :by ((q/ex-intro (lambda [z T] (FIX (succ n) z)) (f y)) <b1>)))

    (have <b> (exists [z T] (FIX (succ n) z))
          :by ((q/ex-elim-rule (lambda [y T] (FIX n y)) (exists [z T] (FIX (succ n) z)))
               Hn <b2>)))

  (have <c> (forall [n nat]
              (exists [z T] (FIX n z)))
        :by ((nats/nat-induct (lambda [n nat]
                                (exists [z T] (FIX n z))))
             <a> <b>))

  (qed <c>))

(defthm nat-recur-rel-sing
  "The singleness part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (q/single (lambda [y T] ((nat-fixpoint-rel x f) n y)))))


(deflemma nat-recur-rel-sing-zero-aux
  [[?T :type] [x T] [f (==> T T)]]
  (forall [y T]
    (==> ((nat-fixpoint-rel x f) zero y)
         (equal x y))))

(proof 'nat-recur-rel-sing-zero-aux-lemma
  (pose FIX := (nat-fixpoint-rel x f))
  (assume [y T
           Hy (FIX zero y)]
    (assume [Hneq (not (equal x y))]
      (pose R := (lambda [n nat]
                   (lambda [z T]
                     (and (FIX n z)
                          (not (and (equal n zero) (equal z y)))))))

      (have <a1> (FIX zero x) :by (nat-fixpoint-zero x f))
      (assume [Hna (and (equal zero zero) (equal x y))]
        (have <a2> p/absurd :by (Hneq (p/and-elim-right Hna))))

      (have <a> (R zero x) :by (p/and-intro <a1> <a2>))

      (assume [n nat
               z T
               Hny (R n z)]
        (have <b1> (FIX n z) :by (p/and-elim-left Hny))
        (have <b2> (FIX (succ n) (f z)) :by ((nat-fixpoint-succ x f) n z <b1>))
        (assume [Hneq (and (equal (succ n) zero) (equal (f z) y))]
          (have <b3> (not (equal (succ n) zero))
                :by (nats/zero-not-succ n))
          (have <b4> p/absurd :by (<b3> (p/and-elim-left Hneq))))
        (have <b> (R (succ n) (f z)) :by (p/and-intro <b2> <b4>)))

      (have <c> (prel/rel-elem R (nat-recur-prop-rel x f))
            :by (p/and-intro <a> <b>))

      (have <d> (R zero y) :by (Hy R <c>))

      (have <e> (and (equal zero zero) (equal y y))
            :by (p/and-intro (eq/eq-refl zero) (eq/eq-refl y)))

      (have <f> p/absurd :by ((p/and-elim-right <d>) <e>)))

    (have <g1> (not (not (equal x y))) :by <f>)
    ;; Q : is classical reasoning mandatory here ?
    (have <g> (equal x y) :by ((classic/not-not-impl (equal x y)) <g1>)))

  (qed <g>))


(deflemma nat-recur-rel-sing-succ-aux
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (forall [y fy T]
      (==> ((nat-fixpoint-rel x f) n y)
           ((nat-fixpoint-rel x f) (succ n) fy)
           (equal fy (f y))))))

(try-proof 'nat-recur-rel-sing-succ-aux-lemma
  (pose FIX := (nat-fixpoint-rel x f))
  (assume [n nat
           y T fy T
           Hn (FIX n y)
           Hsn (FIX (succ n) fy)]
    (have <a> (FIX (succ n) (f y))
          :by (p/and-elim-right ((nat-fixpoint-elem x f) n y Hn)))
    )
  )


(try-proof 'nat-recur-rel-sing-thm
  (pose FIX := (nat-fixpoint-rel x f))
  (pose P := (lambda [n nat] (q/single (lambda [y T] (FIX n y)))))

  "We proceed by induction on n"
  "Base case : n = 0"
  (assume [x1 T x2 T
           Hx1 (FIX zero x1)
           Hx2 (FIX zero x2)]
    (have <a> (equal x x1)
          :by ((nat-recur-rel-sing-zero-aux x f) x1 Hx1))
    (have <b> (equal x x2)
          :by ((nat-recur-rel-sing-zero-aux x f) x2 Hx2))

    (have <c> (equal x1 x2)
          :by (eq/eq-trans (eq/eq-sym <a>) <b>)))

  (have <base> (P zero) :by <c>)

  "Induction step"
  (assume [n nat
           Hn (P n)]
    "We have to show (P (succ n))"

    (assume [fx1 T
             fx2 T
             Hfx1 (FIX (succ n) fx1)
             Hfx2 (FIX (succ n) fx2)]
      (have <a> (exists [x1 T] (FIX n x1))))

    )
)

;; P(n) =
;; (q/single (lambda [y T] (FIX n y)))
;; = (forall [x1 x2 T]
;;      (==> (FIX n x1)
;;           (FIX n x2)
;;           (equal x1 x2))))



;; FIX =
;; (lambda [n nat]
;;   (lambda [y T]
;;     (forall [R (rel nat T)]
;;       (==> (prel/rel-elem R (nat-recur-prop-rel x f))
;;            (R n y)))))
