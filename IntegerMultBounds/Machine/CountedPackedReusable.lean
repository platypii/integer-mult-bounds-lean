import IntegerMultBounds.Machine.CountedPackedRecycle

/-! Reusable fixed-control packed arithmetic with physical cleanup. -/
namespace IntegerMultBounds.Machine.CountedPackedReusable
noncomputable section
variable {a : ℕ}

def forwardProgram (a : ℕ) := seq (CountedPackedArith.program a)
  (extend (CountedPackedRecycle.program false a) 17)
def inverseProgram (a : ℕ) := seq (CountedPackedInverse.program a)
  (extend (CountedPackedRecycle.program true a) 17)

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
variable (V W Z : List Bool) (f g z : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ)
variable (hs : Fin 3 → List Bool)

/-- Forward arithmetic with the scratch payload recycled for the next call. -/
theorem forward_hoare (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (forwardProgram a)
      (fun v => v = CountedPackedArith.bank (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = CountedPackedArith.bank (PackedArith.input
        (PackedArith.v2 q b hb hbq V W Z) (PackedArith.w2 q b hb hbq V W Z) Z
        f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (2720*((Z.length+1)*(q+b+1))) := by
  obtain ⟨l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := PackedArith.lengths q b hb hbq V W Z hV hW
  have hA := CountedPackedArith.forward_hoare q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8 hs
    hV hW hf hf' hg hg' hz hv hc
  have hC := CountedPackedRecycle.recycle_hoare false
    (PackedArith.output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
    V W
    (PackedArith.v1 q b hb hbq V W Z)
    (PackedArith.w1 q b hb hbq V W Z)
    (PackedArith.v2 q b hb hbq V W Z)
    (PackedArith.w2 q b hb hbq V W Z)
    (PackedArith.t1 q b hb hbq V W Z)
    f g rfl rfl rfl rfl rfl rfl rfl
    (by simpa using l8.trans hV.symm) (l10.trans hW.symm) hf hg
  have hE := hoare_extend_eq hC (CountedPackedArith.tail hs)
  have hall := hA.seq hE
  refine hall.consequence (fun _ h => h) ?_ ?_
  · intro v hv
    rw [hv]
    unfold CountedPackedArith.bank
    congr 1
    unfold CountedPackedRecycle.result WordBankCleanup.write PackedArith.output PackedArith.input PackedArith.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [EqualWordReplace.overwrite, l8,l10,hV,hW]
  · simp [CountedPackedRecycle.cost,l2,l4,l6,l8,l10]
    have hnq : Z.length*q ≤ (Z.length+1)*(q+b+1) := by nlinarith
    have hnb : Z.length*b ≤ (Z.length+1)*(q+b+1) := by nlinarith
    have hp : 1 ≤ (Z.length+1)*(q+b+1) := by nlinarith
    omega

/-- Inverse arithmetic with the scratch payload recycled for the next call. -/
theorem inverse_hoare (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (inverseProgram a)
      (fun v => v = CountedPackedArith.bank (PackedInverse.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = CountedPackedArith.bank (PackedInverse.input
        (PackedInverse.v q b hb hbq V W Z) (PackedInverse.w q b hb hbq V W Z) Z
        f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (2720*((Z.length+1)*(q+b+1))) := by
  obtain ⟨l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := PackedInverse.lengths q b hb hbq V W Z hV hW
  have hA := CountedPackedInverse.inverse_hoare q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8 hs
    hV hW hf hf' hg hg' hz hv hc
  have hC := CountedPackedRecycle.recycle_hoare true
    (PackedInverse.output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
    V W
    (PackedInverse.w1 q b hb hbq V W Z)
    (PackedInverse.t q b hb hbq V W Z)
    (PackedInverse.v1 q b hb hbq V W Z)
    (PackedInverse.w q b hb hbq V W Z)
    (PackedInverse.v q b hb hbq V W Z)
    f g rfl rfl rfl rfl rfl rfl rfl
    (by simpa using l10.trans hV.symm) (l8.trans hW.symm) hf hg
  have hE := hoare_extend_eq hC (CountedPackedArith.tail hs)
  have hall := hA.seq hE
  refine hall.consequence (fun _ h => h) ?_ ?_
  · intro v hv
    rw [hv]
    unfold CountedPackedArith.bank
    congr 1
    unfold CountedPackedRecycle.result WordBankCleanup.write PackedInverse.output PackedInverse.input PackedInverse.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [EqualWordReplace.overwrite, l10,l8,hV,hW]
  · simp [CountedPackedRecycle.cost,l2,l4,l6,l8,l10]
    have hnq : Z.length*q ≤ (Z.length+1)*(q+b+1) := by nlinarith
    have hnb : Z.length*b ≤ (Z.length+1)*(q+b+1) := by nlinarith
    have hp : 1 ≤ (Z.length+1)*(q+b+1) := by nlinarith
    omega

end
end IntegerMultBounds.Machine.CountedPackedReusable
