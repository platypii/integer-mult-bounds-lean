module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! The actual shared interior reserve fits selected whole-box volume uniformly in axes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {Q A : ℕ} {U : Type}

theorem selectedReplicaInteriorSharedWorkspace_volume_le (hQ : SS.states ≤ Q)
    (R K cVratio cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.u ≤ H.p → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p →
      H.metadataWidth ≤ cV*H.p → scale*replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤ Sizes.T n := by
  obtain ⟨C,hpoly⟩ := replicaInteriorSharedWorkspace_axis_poly_le hQ R K cVratio cl cw cr cV
  filter_upwards [selectedAxisPolynomial_le_volume (scale*C) 22 22] with n hn
  intro _h i _ H hp ht hu hl hw hr hV
  have hc := Nat.mul_le_mul_left scale (hpoly H hu hl hw hr hV)
  apply hc.trans
  simpa only [hp,ht,Nat.mul_assoc] using hn i

end IntegerMultBounds.MathlibTM2.Cost
