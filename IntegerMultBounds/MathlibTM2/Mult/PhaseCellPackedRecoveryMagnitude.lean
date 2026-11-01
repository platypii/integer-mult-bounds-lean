module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryLocality
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentSolutionMagnitude
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRoundScalars

/-! Ordinary core-job bounds supply normalization's magnitude and width premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

theorem ownedCore_subset_halo (r : PackedNormalizedJob A s) :
    ownedCore s r.coreWidth r.k ⊆ haloVertices s r.a r.b := by
  intro i hi
  obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
  have ha := r.haEq
  have hb := r.hbEq
  apply (mem_haloVertices _ _ i).mpr
  constructor <;> omega

theorem localSolution_round_magnitude (r : PackedNormalizedJob A s) :
    ∀ F ∈ r.Fs, ∀ i ∈ ownedCore s r.coreWidth r.k,
      ‖componentSolution r.localSolution F i‖ ≤ 4*(2 : ℝ)^(r.p+8) := by
  have hdom := dominates_mono (realMatrix s r.t r.p r.u) Finset.univ (haloVertices s r.a r.b)
    (1/(8*(r.p : ℝ))) (Finset.subset_univ _) r.bounds.hdom
  have hbound := componentSolution_stable_bound r.p r.q (by have := r.bounds.hp; omega) r.hpq
    (realMatrix s r.t r.p r.u) (haloVertices s r.a r.b) hdom r.Fs r.hF r.localSolution
    (fun F _ => r.localSolution_solves F)
  intro F hF i hi
  exact componentSolution_round_magnitude r.p r.localSolution F i (hbound F hF i (r.ownedCore_subset_halo hi))

theorem normalization_width (r : PackedNormalizedJob A s) : 2*r.p+13 ≤ r.W := by
  have h := packedRound_dimensions r.p r.u r.l r.targetOut
    (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card
  dsimp only at h
  rw [← r.hqSizing] at h
  have hW := r.hW
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
