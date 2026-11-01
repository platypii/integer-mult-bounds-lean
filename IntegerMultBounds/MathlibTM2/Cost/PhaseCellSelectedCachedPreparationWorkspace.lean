module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! All recovery-preparation scratch is shared and fits selected whole-box volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedCachedRecoveryPreparationWorkspace_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      scale*cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ Sizes.T n := by
  obtain ⟨C,hpoly⟩ := cachedRecoveryPreparationWorkspace_axis_poly_le hQ push c M cw cV
  filter_upwards [selectedAxisPolynomial_le_volume (scale*C) 8 8] with n hn
  intro _h i _ H hp ht hw hV
  have hc := Nat.mul_le_mul_left scale (hpoly H hw hV)
  apply hc.trans
  simpa only [hp,ht,Nat.mul_assoc] using hn i

end IntegerMultBounds.MathlibTM2.Cost
