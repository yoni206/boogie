(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :strings-exp true)
(set-logic ALL_SUPPORTED)
; done setting options


(assert (forall ((x (Seq Int)) (xx (Seq Int)) ) (!  (=> (and (= (seq.len x) (seq.len xx)) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (seq.len x))) (= (seq.nth x i) (seq.nth xx i)))
 :qid |intseqvectorbpl.35:94|
 :skolemid |0|
))) (= x xx))
 :qid |intseqvectorbpl.35:29|
 :skolemid |1|
 :pattern ( (seq.len x) (seq.len xx))
)))
(assert (forall ((s (Seq Int)) (x@@0 Int) ) (! (= (exists ((i@@0 Int) ) (!  (and (and (<= 0 i@@0) (< i@@0 (seq.len s))) (= (seq.nth s i@@0) x@@0))
 :qid |intseqvectorbpl.46:84|
 :skolemid |2|
 :pattern ( (seq.nth s i@@0))
)) (seq.contains s (seq.unit x@@0)))
 :qid |intseqvectorbpl.46:29|
 :skolemid |3|
 :pattern ( (seq.len s) (seq.contains s (seq.unit x@@0)))
)))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun s@0 () (Seq Int))
(declare-fun s@1 () (Seq Int))
(declare-fun s@2 () (Seq Int))
(declare-fun s@3 () (Seq Int))
(push 1)
(set-info :boogie-vc-id test0)
(assert (not
 (=> (= (ControlFlow 0 0) 2164) (let ((anon0_correct  (=> (= s@0 (seq.++ (as seq.empty (Seq Int)) (seq.unit 0))) (=> (and (= s@1 (seq.++ s@0 (seq.unit 1))) (= s@2 (seq.++ s@1 (seq.unit 2)))) (and (=> (= (ControlFlow 0 356) (- 0 2207)) (= (seq.len s@2) 3)) (=> (= (seq.len s@2) 3) (and (=> (= (ControlFlow 0 356) (- 0 2214)) (= (seq.nth s@2 1) 1)) (=> (= (seq.nth s@2 1) 1) (=> (= s@3 (seq.++ (seq.extract s@2 0 1) (seq.unit 3) (seq.extract s@2 (+ 1 1) (- (- (seq.len s@2) 1) 1)))) (and (=> (= (ControlFlow 0 356) (- 0 2236)) (= (seq.nth s@3 0) 0)) (=> (= (seq.nth s@3 0) 0) (and (=> (= (ControlFlow 0 356) (- 0 2245)) (= (seq.nth s@3 1) 3)) (=> (= (seq.nth s@3 1) 3) (=> (= (ControlFlow 0 356) (- 0 2254)) (= (seq.len s@3) 3)))))))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (= (ControlFlow 0 2164) 356) anon0_correct)))
PreconditionGeneratedEntry_correct)))
))
(check-sat)
(pop 1)
; Valid
(declare-fun s@@0 () (Seq Int))
(declare-fun x@@1 () Int)
(push 1)
(set-info :boogie-vc-id test1)
(assert (not
 (=> (= (ControlFlow 0 0) 2274) (let ((anon0_correct@@0  (=> (= (ControlFlow 0 409) (- 0 2373)) (= (seq.nth s@@0 x@@1) 0))))
(let ((PreconditionGeneratedEntry_correct@@0  (=> (and (and (<= 0 x@@1) (< x@@1 (seq.len s@@0))) (and (forall ((i@@1 Int) ) (!  (=> (and (<= 0 i@@1) (< i@@1 (seq.len s@@0))) (= (seq.nth s@@0 i@@1) 0))
 :qid |intseqvectorbpl.82:18|
 :skolemid |4|
)) (= (ControlFlow 0 2274) 409))) anon0_correct@@0)))
PreconditionGeneratedEntry_correct@@0)))
))
(check-sat)
(pop 1)
; Valid
(declare-fun s@@1 () (Seq Int))
(declare-fun x@@2 () Int)
(declare-fun y () Int)
(push 1)
(set-info :boogie-vc-id test2)
(assert (not
 (=> (= (ControlFlow 0 0) 2389) (let ((anon0_correct@@1  (=> (= (ControlFlow 0 483) (- 0 2527)) (<= (seq.nth s@@1 x@@2) (seq.nth s@@1 y)))))
(let ((PreconditionGeneratedEntry_correct@@1  (=> (and (and (and (<= 0 x@@2) (<= x@@2 y)) (< y (seq.len s@@1))) (and (forall ((i@@2 Int) (j Int) ) (!  (=> (and (and (<= 0 i@@2) (<= i@@2 j)) (< j (seq.len s@@1))) (<= (seq.nth s@@1 i@@2) (seq.nth s@@1 j)))
 :qid |intseqvectorbpl.89:18|
 :skolemid |5|
)) (= (ControlFlow 0 2389) 483))) anon0_correct@@1)))
PreconditionGeneratedEntry_correct@@1)))
))
(check-sat)
(pop 1)
; Valid
(declare-fun s@@2 () (Seq Int))
(declare-fun |s'| () (Seq Int))
(push 1)
(set-info :boogie-vc-id equality)
(assert (not
 (=> (= (ControlFlow 0 0) 2546) (let ((anon0_correct@@2  (=> (= (ControlFlow 0 535) (- 0 2637)) (= s@@2 |s'|))))
(let ((PreconditionGeneratedEntry_correct@@2  (=> (= (seq.len s@@2) (seq.len |s'|)) (=> (and (forall ((i@@3 Int) ) (!  (=> (and (<= 0 i@@3) (< i@@3 (seq.len s@@2))) (= (seq.nth s@@2 i@@3) (seq.nth |s'| i@@3)))
 :qid |intseqvectorbpl.103:19|
 :skolemid |6|
)) (= (ControlFlow 0 2546) 535)) anon0_correct@@2))))
PreconditionGeneratedEntry_correct@@2)))
))
(check-sat)
(pop 1)
; Valid
(declare-fun |s'@0| () (Seq Int))
(declare-fun s@@3 () (Seq Int))
(declare-fun pos () Int)
(declare-fun val () Int)
(push 1)
(set-info :boogie-vc-id update)
(assert (not
 (=> (= (ControlFlow 0 0) 2650) (let ((anon0_correct@@3  (=> (and (= |s'@0| (seq.++ (seq.extract s@@3 0 pos) (seq.unit val) (seq.extract s@@3 (+ pos 1) (- (- (seq.len s@@3) pos) 1)))) (= (ControlFlow 0 590) (- 0 2718))) (= |s'@0| s@@3))))
(let ((PreconditionGeneratedEntry_correct@@3  (=> (and (and (<= 0 pos) (< pos (seq.len s@@3))) (and (= (seq.nth s@@3 pos) val) (= (ControlFlow 0 2650) 590))) anon0_correct@@3)))
PreconditionGeneratedEntry_correct@@3)))
))
(check-sat)
(pop 1)
; Valid
(declare-fun s@@4 () (Seq Int))
(declare-fun x@@3 () Int)
(declare-fun b@0 () Bool)
(declare-fun i@0 () Int)
(declare-fun i@1 () Int)
(push 1)
(set-info :boogie-vc-id lookup)
(assert (not
 (=> (= (ControlFlow 0 0) 2744) (let ((GeneratedUnifiedExit_correct  (=> (= (ControlFlow 0 2736) (- 0 2929)) (=> (seq.contains s@@4 (seq.unit x@@3)) b@0))))
(let ((anon5_Then_correct  (=> (= (seq.nth s@@4 i@0) x@@3) (=> (and (= b@0 true) (= (ControlFlow 0 690) 2736)) GeneratedUnifiedExit_correct))))
(let ((anon4_LoopDone_correct  (=> (<= (seq.len s@@4) i@0) (=> (and (= b@0 false) (= (ControlFlow 0 696) 2736)) GeneratedUnifiedExit_correct))))
(let ((anon5_Else_correct  (=> (and (not (= (seq.nth s@@4 i@0) x@@3)) (= i@1 (+ i@0 1))) (and (=> (= (ControlFlow 0 692) (- 0 2882)) (forall ((u Int) ) (!  (=> (and (<= 0 u) (< u i@1)) (not (= x@@3 (seq.nth s@@4 u))))
 :qid |intseqvectorbpl.129:23|
 :skolemid |7|
))) (=> (forall ((u@@0 Int) ) (!  (=> (and (<= 0 u@@0) (< u@@0 i@1)) (not (= x@@3 (seq.nth s@@4 u@@0))))
 :qid |intseqvectorbpl.129:23|
 :skolemid |7|
)) (=> (= (ControlFlow 0 692) (- 0 2910)) (<= 0 i@1)))))))
(let ((anon4_LoopBody_correct  (=> (< i@0 (seq.len s@@4)) (and (=> (= (ControlFlow 0 689) 690) anon5_Then_correct) (=> (= (ControlFlow 0 689) 692) anon5_Else_correct)))))
(let ((anon4_LoopHead_correct  (=> (and (forall ((u@@1 Int) ) (!  (=> (and (<= 0 u@@1) (< u@@1 i@0)) (not (= x@@3 (seq.nth s@@4 u@@1))))
 :qid |intseqvectorbpl.129:23|
 :skolemid |7|
)) (<= 0 i@0)) (and (=> (= (ControlFlow 0 682) 696) anon4_LoopDone_correct) (=> (= (ControlFlow 0 682) 689) anon4_LoopBody_correct)))))
(let ((anon0_correct@@4  (and (=> (= (ControlFlow 0 680) (- 0 2767)) (forall ((u@@2 Int) ) (!  (=> (and (<= 0 u@@2) (< u@@2 0)) (not (= x@@3 (seq.nth s@@4 u@@2))))
 :qid |intseqvectorbpl.129:23|
 :skolemid |7|
))) (=> (forall ((u@@3 Int) ) (!  (=> (and (<= 0 u@@3) (< u@@3 0)) (not (= x@@3 (seq.nth s@@4 u@@3))))
 :qid |intseqvectorbpl.129:23|
 :skolemid |7|
)) (and (=> (= (ControlFlow 0 680) (- 0 2795)) (<= 0 0)) (=> (<= 0 0) (=> (= (ControlFlow 0 680) 682) anon4_LoopHead_correct)))))))
(let ((PreconditionGeneratedEntry_correct@@4  (=> (= (ControlFlow 0 2744) 680) anon0_correct@@4)))
PreconditionGeneratedEntry_correct@@4)))))))))
))
(check-sat)
