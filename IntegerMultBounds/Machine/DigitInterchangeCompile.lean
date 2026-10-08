import IntegerMultBounds.Machine.DigitInterchangeBank

/-! Actual fixed whole-bank execution of all digit-interchange passes. Only the
radix and alphabet determine the program; runtime dimensions occur solely in
supplied descriptor tapes and the correctness/time specification. -/
namespace IntegerMultBounds.Machine.DigitInterchangeCompile
open DigitInterchangeRows DigitInterchangeBank
noncomputable section
variable {O q C E a : ℕ}

abbrev PassStates (q : ℕ) := 7+(CyclicRowCycle.states q+5)+4+(7+(CyclicRowCycle.states q+5)+4)

def localProgram (p : Pass q) (a : ℕ) : Program (LocalTapes q) (PassStates q) a :=
  match p with
  | .splitOuter | .splitInner _ => CyclicRowNormalized.splitProgram q a
  | .mergeOuter | .mergeInner _ => CyclicRowNormalized.mergeProgram q a

def passCost (p : Pass q) (O C E : ℕ) (bs gs es cs : List Bool) : ℕ :=
  match p with
  | .splitOuter | .mergeOuter => CyclicRowNormalized.cost q O (C*(q*E)) bs gs
  | .splitInner _ | .mergeInner _ => CyclicRowNormalized.cost q (O*C) E es cs

def passProgram (p : Pass q) (a : ℕ) := Placement.placed (localProgram p a) (placement p)

private theorem overwrite (f : ℤ → Fin (a+4)) (p : ℤ) (xs ys : List (Fin (a+4)))
    (hlen : xs.length = ys.length) : putWord (putWord f p xs) p ys = putWord f p ys := by
  funext z
  by_cases hlo : z < p
  · rw [putWord_outside _ _ _ _ (Or.inl hlo),putWord_outside _ _ _ _ (Or.inl hlo),putWord_outside _ _ _ _ (Or.inl hlo)]
  · by_cases hhi : p+ys.length ≤ z
    · rw [putWord_outside _ _ _ _ (Or.inr hhi),putWord_outside _ _ _ _ (Or.inr hhi),
        putWord_outside _ _ _ _ (Or.inr (by omega))]
    · have hz : z = p+((z-p).toNat : ℕ) := by omega
      have hi : (z-p).toNat < ys.length := by omega
      rw [hz,WordSegments.get _ _ _ _ hi,WordSegments.get _ _ _ _ hi]

private theorem word_length (x : Array O q C E a) :
    (CyclicRowSplit.sourceWord (outerRows x)).length = O*(q*(C*(q*E))) := by
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords
  simp [List.length_flatten,List.map_ofFn,Function.comp_def,outer_length]

theorem local_hoare (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C) :
    HoareTime (localProgram p a)
      (fun v => v = localBank p x bs gs es cs (passIndex p))
      (fun v => v = localBank p x bs gs es cs (passIndex p+1))
      (passCost p O C E bs gs es cs) := by
  cases p with
  | splitOuter =>
    have h0 : ¬ 1+q+q < 0 := by omega
    have h1 : ¬ 1+q+q < 1 := by omega
    simpa [localProgram,localBank,word,sourceName,roleName,blockHeader,groupHeader,
      headerWord,passIndex,passCost,h0,h1] using DigitInterchangePasses.split_outer x bs gs hb hg
  | splitInner h =>
    simpa [localProgram,localBank,word,sourceName,roleName,blockHeader,groupHeader,
      headerWord,passIndex,passCost] using DigitInterchangePasses.split_inner x h es cs he hc
  | mergeInner h =>
    have hpre (d : Fin q) : 1+d.val < 1+q+h.val := by have := d.isLt; omega
    have hpost (d : Fin q) : 1+d.val < 1+q+h.val+1 := by have := d.isLt; omega
    simpa [localProgram,localBank,word,sourceName,roleName,blockHeader,groupHeader,
      headerWord,passIndex,passCost,hpre,hpost] using DigitInterchangePasses.merge_inner x h es cs he hc
  | mergeOuter =>
    have hpre (d : Fin q) : 1+q+d.val < 1+q+q := by have := d.isLt; omega
    have hpost (d : Fin q) : 1+q+d.val < 1+q+q+1 := by have := d.isLt; omega
    have hh := CyclicRowNormalized.merge_hoare
      (putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows x)))
      (fun _ _ => blank) 0 (fun _ => 0) (outerRows (transpose x)) (C*(q*E))
      (outer_length (transpose x)) bs gs hb hg
    rw [overwrite _ _ _ _ ((word_length x).trans (word_length (transpose x)).symm)] at hh
    simpa [localProgram,localBank,word,sourceName,roleName,blockHeader,groupHeader,
      headerWord,passIndex,passCost,hpre,hpost] using hh

/-- One pass changes exactly its produced streams and preserves the rest of the
complete bank, including every supplied descriptor and restored work clock. -/
theorem pass_hoare (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C) :
    HoareTime (passProgram p a) (fun v => v = bank x bs gs es cs (passIndex p))
      (fun v => v = bank x bs gs es cs (passIndex p+1))
      (passCost p O C E bs gs es cs) := by
  have hh := Placement.hoare_at (local_hoare p x bs gs es cs hb hg he hc)
    (placement p) (bank x bs gs es cs (passIndex p)) (active_local p x bs gs es cs _)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [Placement.replace,frame,← active_local]
  exact Placement.view _ _


def nextPass (k : Fin (2*q+1)) : Pass q :=
  if hk : k.val < q then .splitInner ⟨k.val,hk⟩
  else if hk' : k.val < 2*q then .mergeInner ⟨k.val-q,by omega⟩ else .mergeOuter

theorem nextPass_index (k : Fin (2*q+1)) : passIndex (nextPass k) = k.val+1 := by
  unfold nextPass
  split_ifs <;> simp only [passIndex] <;> omega

theorem nextPass_cost (k : Fin (2*q+1)) (O C E : ℕ) (bs gs es cs : List Bool) :
    passCost (nextPass k) O C E bs gs es cs =
      if k.val < 2*q then CyclicRowNormalized.cost q (O*C) E es cs
      else CyclicRowNormalized.cost q O (C*(q*E)) bs gs := by
  unfold nextPass
  split_ifs <;> simp only [passCost] <;> first | rfl | omega

def prefixStates (q : ℕ) : ℕ → ℕ
  | 0 => PassStates q
  | n+1 => prefixStates q n+PassStates q

def prefixProgram (q a : ℕ) : (n : ℕ) → n ≤ 2*q+1 → Program (TapeCount q) (prefixStates q n) a
  | 0,_ => passProgram .splitOuter a
  | n+1,hn => seq (prefixProgram q a n (by omega)) (passProgram (nextPass ⟨n,by omega⟩) a)

def prefixCost (q O C E : ℕ) (bs gs es cs : List Bool) (n : ℕ) : ℕ :=
  CyclicRowNormalized.cost q O (C*(q*E)) bs gs+
    min n (2*q)*CyclicRowNormalized.cost q (O*C) E es cs+
    (if 2*q < n then CyclicRowNormalized.cost q O (C*(q*E)) bs gs else 0)+n

private theorem prefixCost_succ (O C E : ℕ) (bs gs es cs : List Bool) (k : Fin (2*q+1)) :
    prefixCost q O C E bs gs es cs (k.val+1) =
      prefixCost q O C E bs gs es cs k.val+passCost (nextPass k) O C E bs gs es cs+1 := by
  rw [nextPass_cost]
  unfold prefixCost
  by_cases hk : k.val < 2*q
  · have hle : k.val ≤ 2*q := by omega
    have hs : k.val+1 ≤ 2*q := by omega
    simp only [Nat.min_eq_left hle,Nat.min_eq_left hs,ite_eq_left hk,
      ite_eq_right (show ¬ 2*q < k.val from by omega),ite_eq_right (show ¬ 2*q < k.val+1 from by omega)]
    ring
  · have he : k.val = 2*q := by have := k.isLt; omega
    rw [he]
    simp only [Nat.min_self,Nat.min_eq_right (by omega : 2*q ≤ 2*q+1),lt_self_iff_false,
      ite_false,Nat.lt_succ_self,ite_true]
    ring

theorem prefix_hoare (x : Array O q C E a) (bs gs es cs : List Bool)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (n : ℕ) (hn : n ≤ 2*q+1) :
    HoareTime (prefixProgram q a n hn) (fun v => v = bank x bs gs es cs 0)
      (fun v => v = bank x bs gs es cs (n+1)) (prefixCost q O C E bs gs es cs n) := by
  induction n with
  | zero =>
    simpa only [prefixProgram,prefixStates,prefixCost,Nat.zero_min,zero_mul,Nat.not_lt_zero,ite_false,
      Nat.add_zero,passIndex,passCost] using pass_hoare .splitOuter x bs gs es cs hb hg he hc
  | succ n ih =>
    have hp := pass_hoare (nextPass (q := q) ⟨n,by omega⟩) x bs gs es cs hb hg he hc
    rw [nextPass_index] at hp
    have hh := (ih (by omega)).seq hp
    apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
    have hcost := prefixCost_succ (q := q) O C E bs gs es cs ⟨n,by omega⟩
    simpa only [Fin.val_mk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using le_of_eq hcost.symm

def program (q a : ℕ) := prefixProgram q a (2*q+1) le_rfl

def input (x : Array O q C E a) (bs gs es cs : List Bool) := bank x bs gs es cs 0
def output (x : Array O q C E a) (bs gs es cs : List Bool) := bank x bs gs es cs (2*q+2)

/-- Every split, transposed inner merge and final merge is run on one bank.
All joins are charged, and every payload head returns to its original zero. -/
theorem realizes_hoare (x : Array O q C E a) (bs gs es cs : List Bool)
    (hq : 0 < q) (hO : 0 < O) (hC : 0 < C) (hE : 0 < E)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs)
    (ce : GrowingCounterData.Canonical es) (cc : GrowingCounterData.Canonical cs) :
    HoareTime (program q a) (fun v => v = input x bs gs es cs)
      (fun v => v = output x bs gs es cs) ((597+2*q)*(O*(q*(C*(q*E))))) := by
  have hh := prefix_hoare x bs gs es cs hb hg he hc (2*q+1) le_rfl
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  have hbnd := DigitInterchangePasses.passes_cost_linear bs gs es cs hq hO hC hE hb hg he hc cb cg ce cc
  have hcost : prefixCost q O C E bs gs es cs (2*q+1) =
      2*CyclicRowNormalized.cost q O (C*(q*E)) bs gs+
        2*q*CyclicRowNormalized.cost q (O*C) E es cs+2*q+1 := by
    simp only [prefixCost,Nat.min_eq_right (by omega : 2*q ≤ 2*q+1),Nat.lt_succ_self,ite_true]
    ring
  rw [hcost]
  exact hbnd

/-- The original source is overwritten with exactly the transposed word; every
intermediate leaf and all metadata are explicit above. -/
theorem output_source (x : Array O q C E a) (bs gs es cs : List Bool) :
    (output x bs gs es cs).head (slot .source) = 0 ∧
    (output x bs gs es cs).tape (slot .source) =
      putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows (transpose x))) := by
  simp only [output,bank_head,bank_tape,head,word]
  rw [ite_eq_left (by omega : 1+q+q < 2*q+2)]
  trivial

theorem input_source (x : Array O q C E a) (bs gs es cs : List Bool) :
    (input x bs gs es cs).head (slot .source) = 0 ∧
    (input x bs gs es cs).tape (slot .source) =
      putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows x)) := by
  simp [input,head,word]

end
end IntegerMultBounds.Machine.DigitInterchangeCompile
