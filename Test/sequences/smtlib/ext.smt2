(set-logic ALL)
(declare-fun s () (Seq Int))
(declare-fun ss () (Seq Int))

; (declare-fun k () Int)
; (assert (distinct (seq.nth s k) (seq.nth ss k)))
; (assert (<= 0 k))
; (assert (< k (seq.len s)))

(assert (distinct s ss))
(assert (= (seq.len s) (seq.len ss)))
(assert (= (seq.len s) (seq.len ss)))
; (assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len s))) (= (seq.nth s i) (seq.nth ss i)))))
(check-sat)
