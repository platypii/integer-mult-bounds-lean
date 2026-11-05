module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamCrops

/-! Expose the next certified bank from the physical-order seam archive.
The remaining banks are the borrowed source suffix of singleton publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {A s : ℕ} [NeZero s]

theorem seamArchiveHandoff (p width k : ℕ) (ks : List ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (banks : List (List (List GaussianInt)))
    (h : List.Forall₂ (SeamCropRows p width r J) (k::ks) banks)
    (tail : List (Fin (A+4))) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p width r J k rows ∧
      List.Forall₂ (SeamCropRows p width r J) ks rest ∧
      ((banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++tail) =
        cstream A (2*p+13) rows.flatten++
          ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++tail) := by
  cases h with
  | cons hrow hrest =>
    exact ⟨_,_,rfl,hrow,hrest,by simp only [List.map_cons,List.flatten_cons,List.append_assoc]⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
