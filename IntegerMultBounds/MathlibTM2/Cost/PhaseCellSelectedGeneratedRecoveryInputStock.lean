module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryInputExec
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedRecoveryInput
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedFirstCachedRecovery

/-! Absolute stock for the complete physical caller from its ordinary input
bank: initial storage and shared execution workspace are both charged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedGeneratedRecoveryInput_total_stock_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct cH : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)) (target : ℕ),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      target ≤ ct*Sizes.p n → H.target ≤ cH*Sizes.p n → H.rhsExp = 2 →
      ∀ (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H (target+1) X)
        htargetRecovery (inp : List (Bool ⊕ Bool)) (out : List Bool),
      generatedRecoveryInputStock H inp out+
        generatedFirstCachedReplicaRecoveryWorkspace H (B.problem htargetRecovery) (target+1) hR hQ push c M R K ≤
        inp.length+out.length+11*Sizes.T n+C*H.Fs.length*H.t*H.p := by
  obtain ⟨Ci,hi⟩ := selectedGeneratedRecoveryInputStock_le cH 2
  obtain ⟨Cw,hw⟩ := selectedGeneratedFirstCachedRecoveryWorkspace_le hR hQ push c M R K ct cH
  refine ⟨Ci+Cw,?_⟩
  filter_upwards [hi,hw] with n hinit hwork
  intro h i _ H target hp ht hl hu htarget hHtarget hrhs X B hsetup inp out
  have hrhsBound : H.rhsExp ≤ 2*Sizes.p n := by have := h.thirteen_le_p; omega
  have hs := hinit h i H hp ht hl hu hHtarget hrhsBound inp out
  have hh := hwork h i H target hp ht hl hu htarget hHtarget hrhs X B hsetup
  nlinarith only [hs,hh]

end IntegerMultBounds.MathlibTM2.Cost
