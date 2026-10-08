import IntegerMultBounds.Machine.DigitInterchangeRows

/-! Physical pass contracts for single-digit interchange. Both split levels and
both inverse merge levels use fixed counted tape machines. The intermediate
words match literally; only the fixed pair of radix-role indices is exchanged.
Joining the passes on one complete bank remains separate. -/
namespace IntegerMultBounds.Machine.DigitInterchangePasses
open DigitInterchangeRows CyclicRowSplit
variable {O q C E a : ℕ}

/-- First physical split, separating the earlier radix digit. -/
theorem split_outer (x : Array O q C E a) (bs gs : List Bool)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O) :
    HoareTime (CyclicRowNormalized.splitProgram q a)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (sourceWord (outerRows x)))
        (fun _ _ => blank) 0 (fun _ => 0) bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (sourceWord (outerRows x)))
        (fun h => putWord (fun _ => blank) 0 (sourceWord (innerRows x h)))
        0 (fun _ => 0) bs) gs)
      (CyclicRowNormalized.cost q O (C*(q*E)) bs gs) := by
  simpa only [outer_role_inner_source] using
    CyclicRowNormalized.split_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
      (outerRows x) (C*(q*E)) (outer_length x) bs gs hb hg

/-- Each second-level split separates the later radix digit, retaining middle
and suffix fields in their literal original order. -/
theorem split_inner (x : Array O q C E a) (h : Fin q) (es cs : List Bool)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C) :
    HoareTime (CyclicRowNormalized.splitProgram q a)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (sourceWord (innerRows x h)))
        (fun _ _ => blank) 0 (fun _ => 0) es) cs)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (sourceWord (innerRows x h)))
        (fun d => putWord (fun _ => blank) 0 (roleWord (innerRows x h) d))
        0 (fun _ => 0) es) cs)
      (CyclicRowNormalized.cost q (O*C) E es cs) :=
  CyclicRowNormalized.split_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    (innerRows x h) E (inner_length x h) es cs he hc

/-- Read leaf (d,h) into output stream h: the permutation is fixed wiring,
independent of every runtime field length. Heads are physically restored. -/
theorem merge_inner (x : Array O q C E a) (h : Fin q) (es cs : List Bool)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C) :
    HoareTime (CyclicRowNormalized.mergeProgram q a)
      (fun v => v = bank (CyclicRowCopy.bank (fun _ => blank)
        (fun d => putWord (fun _ => blank) 0 (roleWord (innerRows x d) h))
        0 (fun _ => 0) es) cs)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (roleWord (outerRows (transpose x)) h))
        (fun d => putWord (fun _ => blank) 0 (roleWord (innerRows x d) h))
        0 (fun _ => 0) es) cs)
      (CyclicRowNormalized.cost q (O*C) E es cs) := by
  simpa only [inner_role_transpose,← outer_role_inner_source] using
    CyclicRowNormalized.merge_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
      (innerRows (transpose x) h) E (inner_length (transpose x) h) es cs he hc

/-- Last physical merge serializes the transposed array. -/
theorem merge_outer (x : Array O q C E a) (bs gs : List Bool)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O) :
    HoareTime (CyclicRowNormalized.mergeProgram q a)
      (fun v => v = bank (CyclicRowCopy.bank (fun _ => blank)
        (fun h => putWord (fun _ => blank) 0 (roleWord (outerRows (transpose x)) h))
        0 (fun _ => 0) bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank
        (putWord (fun _ => blank) 0 (sourceWord (outerRows (transpose x))))
        (fun h => putWord (fun _ => blank) 0 (roleWord (outerRows (transpose x)) h))
        0 (fun _ => 0) bs) gs)
      (CyclicRowNormalized.cost q O (C*(q*E)) bs gs) :=
  CyclicRowNormalized.merge_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    (outerRows (transpose x)) (C*(q*E)) (outer_length (transpose x)) bs gs hb hg

/-- Sum of the actual pass costs, including one join between successive passes.
This is a cost estimate, not yet a whole-bank compilation theorem. -/
theorem passes_cost_linear (bs gs es cs : List Bool)
    (hq : 0 < q) (hO : 0 < O) (hC : 0 < C) (hE : 0 < E)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs)
    (ce : GrowingCounterData.Canonical es) (cc : GrowingCounterData.Canonical cs) :
    2*CyclicRowNormalized.cost q O (C*(q*E)) bs gs+
      2*q*CyclicRowNormalized.cost q (O*C) E es cs+2*q+1 ≤
      (597+2*q)*(O*(q*(C*(q*E)))) := by
  have hout := CyclicRowNormalized.cost_linear (C*(q*E)) bs gs hq hO
    (Nat.mul_pos hC (Nat.mul_pos hq hE)) hb hg cb cg
  have hin := CyclicRowNormalized.cost_linear E es cs hq (Nat.mul_pos hO hC) hE he hc ce cc
  have hm := Nat.mul_le_mul_left (2*q) hin
  have hV : 0 < O*(q*(C*(q*E))) := Nat.mul_pos hO (Nat.mul_pos hq (Nat.mul_pos hC (Nat.mul_pos hq hE)))
  have hj := Nat.mul_le_mul_left (2*q+1) hV
  nlinarith

end IntegerMultBounds.Machine.DigitInterchangePasses
