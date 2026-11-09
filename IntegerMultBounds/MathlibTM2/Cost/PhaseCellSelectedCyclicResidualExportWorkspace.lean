module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerExport
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Residual export has linear replica traffic and shared linear control storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem exportCyclicResidualRowsCost_le_linear (replicas n N w : ℕ) :
    exportCyclicResidualRowsCost replicas n N w ≤
      (137*replicas+100)*(n+N+1)*(w+1) := by
  have hb := cyclicReplicaBoundaryBatchCost_le replicas n N w
  unfold exportCyclicResidualRowsCost initializedCyclicReplicaBoundaryBatchCost boundaryFoldCountersCost
  nlinarith only [hb,Nat.zero_le (n*w),Nat.zero_le (N*w)]

theorem selectedCyclicResidualExportWorkspace_le (cw : ℕ) :
    let push := cyclicResidualExportPush (Q := Q) (A := A) (U := U)
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K : ReplicaHaloProblem (Sizes.s m i)) (n N : ℕ),
      H.wordWidth ≤ cw*Sizes.p m → K.wordWidth ≤ cw*Sizes.p m →
      n ≤ Sizes.s m i → N ≤ Sizes.s m i →
      cyclicReplicaConsumerExportWorkspace (Q := Q) (A := A) (U := U) H K n N ≤
        (411*push*(cw+1)+8)*H.Fs.length*Sizes.t m i*Sizes.p m+Sizes.T m := by
  dsimp only
  let push := cyclicResidualExportPush (Q := Q) (A := A) (U := U)
  let C := 24*cw+34+300*push*(cw+1)
  filter_upwards [selectedAxisPolynomial_le_volume C 1 1] with m hv
  intro h i _ H K n N hwH hwK hn hN
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have hunit : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hHN : H.span ≤ Sizes.t m i := by have := H.span_fit; have := h.good.lt i; omega
  have hKN : K.span ≤ Sizes.t m i := by have := K.span_fit; have := h.good.lt i; omega
  have hvolH := Nat.mul_le_mul hHN hwH
  have hvolK := Nat.mul_le_mul hKN hwK
  have hwLinear := Nat.mul_le_mul_left (cw*Sizes.p m) ht
  have hwidth : H.wordWidth+1 ≤ (cw+1)*Sizes.p m := by nlinarith only [hwH,hp]
  have hrows : n+N+1 ≤ 3*Sizes.t m i := by have := h.good.lt i; omega
  have hshape := Nat.mul_le_mul hrows hwidth
  have hexport := Nat.mul_le_mul_left push
    (exportCyclicResidualRowsCost_le_linear H.Fs.length n N H.wordWidth)
  have htraffic := Nat.mul_le_mul_left (push*(137*H.Fs.length+100)) hshape
  have hvolume := hv i
  simp only [pow_one] at hvolume
  have hshared : 8*H.wordWidth+8*(H.span*H.wordWidth)+8*(K.span*K.wordWidth)+34+
      300*push*(cw+1)*Sizes.t m i*Sizes.p m ≤ Sizes.T m := by
    dsimp only [C] at hvolume
    nlinarith only [hvolume,hvolH,hvolK,hwH,hwLinear,hunit]
  have hcount := Nat.mul_le_mul_left (8*H.Fs.length) hunit
  unfold cyclicReplicaConsumerExportWorkspace
  change _ ≤ (411*push*(cw+1)+8)*H.Fs.length*Sizes.t m i*Sizes.p m+Sizes.T m
  change push*_ ≤ _ at hexport
  nlinarith only [hexport,htraffic,hshared,hcount]

end IntegerMultBounds.MathlibTM2.Cost
