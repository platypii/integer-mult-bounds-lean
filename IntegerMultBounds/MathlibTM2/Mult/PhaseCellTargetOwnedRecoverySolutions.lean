module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! The constructed targets solve the original principal matrix with the exact
half-grid RHS used by input conversion. Final scaling must account for this half. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s t p u l : ℕ} [NeZero s] {α gap : ℝ}

theorem ownedTargets_solves (h : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let active := haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
    List.Forall₂ (fun F z =>
      Solves (realMatrix s t p u) active (fun i => (z i).re)
        (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).re) ∧
      Solves (realMatrix s t p u) active (fun i => (z i).im)
        (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).im))
      Fs (h.ownedTargets target L k hnear hL ha hb hfit Fs) := by
  dsimp only
  let bounds := h.ownedBounds target L k hnear hL ha hb hfit
  let q := packedHaloPrecision p l s t u (target+1) 2
    (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
  let y := fun F : ZMod s → GaussianInt =>
    GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
  change List.Forall₂ _ Fs ((selectedRhsFields s Fs).map (componentSolution y))
  simp only [selectedRhsFields,List.map_map,Function.comp_def]
  rw [List.forall₂_map_right_iff,List.forall₂_same]
  intro F hmem
  have hpq : p+1 ≤ q := by
    dsimp [q,packedHaloPrecision,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  have hshift (i : ZMod s) : value q ((2 : GaussianInt)^(q-p-1)*F (rowIndex s t i)) =
      (1/2 : ℂ)*value p (F (rowIndex s t i)) :=
    (packedInputShift_value_fits p q hpq _ (hF F hmem _)).1
  have hs := componentSolution_solves q (q-p-1) (realMatrix s t p u)
    (haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u))
    y (fun i => F (rowIndex s t i))
    (GeneratedRecoveryJob.solutionMap_solves bounds
      (fun i => (2 : GaussianInt)^(q-p-1)*realPartWord (F (rowIndex s t i))))
    (GeneratedRecoveryJob.solutionMap_solves bounds
      (fun i => (2 : GaussianInt)^(q-p-1)*imagPartWord (F (rowIndex s t i))))
  simpa only [hshift] using hs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
