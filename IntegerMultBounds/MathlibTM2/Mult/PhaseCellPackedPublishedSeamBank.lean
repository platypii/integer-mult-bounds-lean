module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPublishedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationPending

/-! Match the actual packed publication bank to the seam completion target list,
including the producer's reversed replica order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.LayerMachine
variable {A s t B L width : ℕ} [NeZero s] [NeZero t] {batch : PackedExactBatch A s t B L}

theorem Rows.published_seam_bank_good (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun job => job.k) = g.indices) (hw : 0 < width)
    (p : ℕ) (F : Fin B → ZMod s → GaussianInt) (r : FamilyDispatchInput s A)
    (hinputs : List.ofFn F = r.inputs.reverse)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ job ∈ batch.records, job.p = p)
    (hwidth : ∀ job ∈ batch.records, job.coreWidth = width)
    (hF : ∀ job ∈ batch.records, job.Fs = r.inputs.reverse)
    (hJ : ∀ job ∈ batch.records, batch.J job = J r)
    (ambient : Fin B → List (Fin (A+4))) (hlen : ∀ j, (ambient j).length = s*batch.W) :
    List.Forall₂ (fun target line => line.length = s*batch.W ∧
      ∀ k ∈ g.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p batch.W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p batch.W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J)
      (List.ofFn (fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j))) := by
  have htargets : (List.ofFn (fun j => (((2:ℂ)^inverseNormalizationShift p)⁻¹ • J r)
      ((1/2:ℂ) • fun i => value p (F j i)))) = seamPublicationTargets p r J := by
    rw [seamPublicationTargets,←hinputs,List.map_ofFn]
    rfl
  have hgood := rows.published_bank_good g hkeys hw p F (J r) hp hwidth
    (fun job hj => (hF job hj).trans hinputs.symm) hJ ambient hlen
  rw [htargets] at hgood
  exact hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
