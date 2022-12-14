(ns latte-nats.times
  "The multiplication defined on ℕ."

  (:refer-clojure :exclude [and or not int = + *])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed search-theorem]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.algebra :as alg]

            [latte-sets.quant :as sq :refer [forall-in]]
            
            [latte-nats.core :as nats :refer [nat = zero succ]]
            [latte-nats.rec :as rec]
            [latte-nats.plus :as plus :refer [+]]
                       ))

(definition mult-prop
  "The property of the multiplication of `m` to a natural integer."
  [[m nat]]
  (lambda [g (==> nat nat)]
    (and (= (g zero) zero)
         (forall [n nat]
           (= (g (succ n)) (+ m (g n)))))))

(defthm mult-unique
  "The unicity of the multiplication function, through [[mult-prop]]."
  [[m nat]]
  (q/unique (mult-prop m)))

(proof 'mult-unique
  (qed (rec/nat-recur zero (lambda [n nat] (+ m n)))))


(definition times
  "The function that multiplies `m` to a natural number"
  [[m nat]]
  (q/the (mult-unique m)))

(definition *
  "The function that multiplies `m` with `n`."
  [[m nat] [n nat]]
  ((times m) n))


(defthm times-prop
  [[m nat]]
  (and (= (* m zero) zero)
       (forall [n nat]
         (= (* m (succ n))
            (+ m (* m n))))))

(proof 'times-prop
  (qed (q/the-prop (mult-unique m))))

;; now that we have the main property we can make
;; the basic definitions opaque
(u/set-opacity! #'mult-prop true)

(defthm times-zero
  [[n nat]]
  (= (* n zero)
     zero))

(proof 'times-zero
  (qed (p/and-elim-left (times-prop n))))


(defthm times-succ
  [[m nat] [n nat]]
  (= (* m (succ n))
     (+ m (* m n))))

(proof 'times-succ
  (qed ((p/and-elim-right (times-prop m)) n)))

(defthm times-succ-swap-right
  [[m nat] [n nat]]
  (= (* m (succ n))
     (+ (* m n) m)))

(proof 'times-succ-swap-right
  (have <a> (= (+ m (* m n))
               (+ (* m n) m))
        :by (plus/plus-commute m (* m n)))
  (qed (eq/rewrite (times-succ m n) <a>)))

;; from now on times-prop is not needed
(u/set-opacity! #'times-prop true)
(u/set-opacity! #'times true)
(u/set-opacity! #'* true)

(defthm times-zero-swap
  [[n nat]]
  (= (* zero n)
     zero))

(proof 'times-zero-swap
  "This is by induction on `n`."
  (pose P := (lambda [k nat] (= (* zero k)
                                zero)))
  "Base case: n=0"
  (have <a> (P zero)
        :by (times-zero zero))
  "Inductive case"
  (assume [k nat
           Hind (= (* zero k)
                   zero)]
    (have <b1> (= (* zero (succ k))
                  (+ zero (* zero k)))
          :by (times-succ zero k))
    (have <b2> (= (* zero (succ k))
                  (* zero k))
          :by (eq/rewrite <b1> (plus/plus-zero-swap (* zero k))))
    (have <b> (P (succ k))
          :by (eq/rewrite <b2> Hind)))
  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) n)))

(defthm times-succ-swap-left
  [[n nat] [m nat]]
  (= (* (succ n) m)
     (+ m (* n m))))

;; This one is a fairly cumbersome one ...
(proof 'times-succ-swap-left
  "We proceed by induction on m"
  (pose P := (lambda [k nat] (= (* (succ n) k)
                                (+ k (* n k)))))
  "Base case m=0"
  (have <a1> (= (* (succ n) zero)
                zero)
        :by (times-zero (succ n)))
  (have <a2> (= (+ zero (* n zero))
                (+ zero zero))
        :by (eq/eq-cong (lambda [k nat] (+ zero k))
                        (times-zero n)))
  (have <a3> (= (+ zero (* n zero))
                zero)
        :by (eq/rewrite <a2> (plus/plus-zero zero)))
  (have <a4> (= zero
                (+ zero (* n zero)))
        :by (eq/eq-sym <a3>))
  (have <a> (P zero) :by (eq/eq-trans <a1> <a4>))
  "Inductive case"
  (assume [k nat
           Hind (= (* (succ n) k)
                   (+ k (* n k)))]
    (have <b1> (= (* (succ n) (succ k))
                  (+ (succ n) (* (succ n) k)))
          :by (times-succ (succ n) k))

    (have <b2> (= (+ (succ n) (* (succ n) k))
                  (+ (succ n) (+ k (* n k))))
          :by (eq/eq-cong (lambda [j nat] (+ (succ n) j))
                          Hind))

    (have <b2'> (= (+ (succ n) (* (succ n) k))
                  (+ (succ n) (+ (* n k) k)))
          :by (eq/rewrite <b2> (plus/plus-commute k (* n k))))

    (have <b3> (= (+ (succ n) (* (succ n) k))
                  (succ (+ n (+ (* n k) k))))
          :by (eq/rewrite <b2'> (plus/plus-succ-swap n (+ (* n k) k))))
    
    (have <b4> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (+ n (* n k)) k)))
          :by (eq/rewrite <b3> (plus/plus-assoc n (* n k) k)))

    (have <b5> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (+ (* n k) n) k)))
          :by (eq/rewrite <b4> (plus/plus-commute n (* n k))))

    (have <b6> (= (+ (succ n) (* (succ n) k))
                  (succ (+ (* n (succ k)) k)))
          :by (eq/rewrite <b5> (eq/eq-sym (times-succ-swap-right n k))))

    (have <b7> (= (+ (succ n) (* (succ n) k))
                  (+ (* n (succ k)) (succ k)))
          :by (eq/rewrite <b6> (plus/plus-succ-sym (* n (succ k)) k)))

    (have <b8> (= (+ (succ n) (* (succ n) k))
                  (+ (succ k) (* n (succ k))))
          :by (eq/rewrite <b7> (plus/plus-commute (* n (succ k)) (succ k))))

    (have <b> (P (succ k))
          :by (eq/eq-trans <b1> <b8>)))

  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) m)))

(defthm times-commute
  "Commutativity of multiplication."
  [[m nat] [n nat]]
  (= (* m n) (* n m)))


(proof 'times-commute
  "By induction on `m`."
  (pose P := (lambda [k nat] (= (* k n) (* n k))))
  "Base case."
  (have <a1> (= (* zero n) zero)
        :by (times-zero-swap n))
  (have <a2> (= zero (* n zero))
        :by (eq/eq-sym (times-zero n)))  
  (have <a> (P zero) :by (eq/eq-trans <a1> <a2>))
  "Inductive cases."
  (assume [k nat
           Hind (= (* k n) (* n k))]
    (have <b1> (= (* (succ k) n)
                  (+ n (* k n)))
          :by (times-succ-swap-left k n))
    (have <b2> (= (* (succ k) n)
                  (+ n (* n k)))
          :by (eq/rewrite <b1> Hind))
    (have <b>(P (succ k))
          :by (eq/rewrite <b2> (eq/eq-sym (times-succ n k)))))

  "Conclusion"
  (qed (((nats/nat-induct P) <a> <b>) m)))


    

