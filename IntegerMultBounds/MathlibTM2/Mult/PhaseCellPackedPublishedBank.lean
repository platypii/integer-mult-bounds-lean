module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProperPublicationBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassPublicationSpec

/-! A producer's actual class rows yield the proper-bank handoff certificate
for the exact class-scatter endpoint returned by published class execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s t B L width : ℕ} [NeZero s] [NeZero t] {batch : PackedExactBatch A s t B L}

theorem Rows.published_bank_good (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) (hw : 0 < width)
    (p : ℕ) (F : Fin B → ZMod s → GaussianInt)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ r ∈ batch.records, r.p = p)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width)
    (hF : ∀ r ∈ batch.records, r.Fs = List.ofFn F)
    (hJ : ∀ r ∈ batch.records, batch.J r = J)
    (ambient : Fin B → List (Fin (A+4))) (hlen : ∀ j, (ambient j).length = s*batch.W) :
    List.Forall₂ (fun target line => line.length = s*batch.W ∧
      ∀ k ∈ g.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p batch.W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p batch.W line) target (3/(2:ℝ)^p))
      (List.ofFn (fun j => (((2:ℂ)^inverseNormalizationShift p)⁻¹ • J)
        ((1/2:ℂ) • fun i => value p (F j i))))
      (List.ofFn (fun j => g.output batch.W hw (rows.classRows g hkeys j) (ambient j))) :=
  g.output_bank_good p batch.W hw _ (3/(2:ℝ)^p) (rows.classRows g hkeys) ambient
    (rows.classRows_length g hkeys hwidth) hlen (rows.classRows_spec g hkeys p F J hp hwidth hF hJ)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
