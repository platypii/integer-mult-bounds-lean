import IntegerMultBounds.Networks.BinaryPhase
import IntegerMultBounds.Networks.BinaryRowProgram
import Mathlib.LinearAlgebra.Basis.Prod

/-! Extend an actual nondegenerate phase-subspace basis by its orthogonal
complement, retaining its literal first coordinates. The resulting ambient
binary basis has a proved finite row-addition schedule. -/
namespace IntegerMultBounds.Networks.BinaryPhaseBasisExtension
noncomputable section
open Module
variable {h d : ℕ}
abbrev Address (h : ℕ) := Fin h → ZMod 2

variable (B : LinearMap.BilinForm (ZMod 2) (Address h)) (hs : B.IsSymm)
    (W : Submodule (ZMod 2) (Address h)) (hw : (B.restrict W).Nondegenerate)
    (b : Basis (Fin d) (ZMod 2) W)

abbrev complement := B.orthogonal W
abbrev Index := Fin d ⊕ Fin (finrank (ZMod 2) (complement B W))

def splitEquiv : (W × complement B W) ≃ₗ[ZMod 2] Address h :=
  Submodule.prodEquivOfIsCompl W (complement B W)
    (B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hw)

def sumBasis : Basis (Index (d := d) B W) (ZMod 2) (Address h) :=
  (b.prod (Module.finBasis (ZMod 2) (complement B W))).map (splitEquiv B hs W hw)

include hs hw b in
theorem dimension : d + finrank (ZMod 2) (complement B W) = h := by
  have hd := finrank_eq_card_basis (sumBasis B hs W hw b)
  simpa using hd.symm

def indexEquiv : Index (d := d) B W ≃ Fin h :=
  finSumFinEquiv.trans (finCongr (dimension B hs W hw b))

def ambientBasis : Basis (Fin h) (ZMod 2) (Address h) :=
  (sumBasis B hs W hw b).reindex (indexEquiv B hs W hw b)

def slot (i : Fin d) : Fin h := indexEquiv B hs W hw b (Sum.inl i)

theorem slot_val (i : Fin d) : (slot B hs W hw b i).val = i.val := rfl

theorem retains (i : Fin d) : ambientBasis B hs W hw b (slot B hs W hw b i) = (b i : Address h) := by
  simp only [ambientBasis, slot, Basis.reindex_apply, Equiv.symm_apply_apply,
    sumBasis, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply]
  change splitEquiv B hs W hw (b i, 0) = _
  simp [splitEquiv]

/-- The retained coordinates are exactly the phase construction's bilinear
controls, not merely coordinates in an unrelated ambient basis. -/
theorem selected_coordinate
    (hgram : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (x : Address h) (i : Fin d) :
    (ambientBasis B hs W hw b).equivFun x (slot B hs W hw b i) = B (b i) x := by
  simp only [ambientBasis, Basis.equivFun_apply, Basis.repr_reindex_apply, slot,
    Equiv.symm_apply_apply]
  change b.repr ((splitEquiv B hs W hw).symm x).1 i = _
  rw [BinaryPhase.basis_repr B W b hgram]
  let y := (splitEquiv B hs W hw).symm x
  have hx : (y.1 : Address h) + (y.2 : Address h) = x := by
    have hh := (splitEquiv B hs W hw).apply_symm_apply x
    simpa [splitEquiv, y] using hh
  have hz : B (b i) (y.2 : Address h) = 0 := y.2.property (b i) (b i).property
  change B (b i) (y.1 : Address h) = B (b i) x
  rw [← hx, map_add, hz, add_zero]

def word : List (BinaryRowProgram.Op (Fin h)) :=
  BinaryRowProgram.basisWord (Pi.basisFun (ZMod 2) (Fin h)) (ambientBasis B hs W hw b)

theorem word_run (x : Address h) :
    BinaryRowProgram.run (word B hs W hw b) x = (ambientBasis B hs W hw b).equivFun x := by
  have hh := BinaryRowProgram.basisWord_run (Pi.basisFun (ZMod 2) (Fin h))
    (ambientBasis B hs W hw b) x
  simpa [word] using hh

theorem word_selected
    (hgram : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (x : Address h) (i : Fin d) :
    BinaryRowProgram.run (word B hs W hw b) x (slot B hs W hw b i) = B (b i) x := by
  rw [word_run, selected_coordinate B hs W hw b hgram]

/-- The original projector phase is exactly a diagonal phase on the literal
coordinates produced by the proved row-addition word. -/
theorem phase_run
    (hsym : (Labels.binary h).IsSymm)
    (hnondeg : ((Labels.binary h).restrict W).Nondegenerate)
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0)
    (x : Address h) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary h) hsym W hnondeg x) =
      ∑ i : Fin d, BinaryPhase.weightPhase (b i : Address h) *
        BinaryPhase.bitLift (BinaryRowProgram.run (word (Labels.binary h) hsym W hnondeg b) x
          (slot (Labels.binary h) hsym W hnondeg b i)) := by
  rw [BinaryPhase.weightPhase_project hsym W hnondeg b hgram]
  apply Finset.sum_congr rfl
  intro i _
  rw [word_selected (Labels.binary h) hsym W hnondeg b hgram]

end
end IntegerMultBounds.Networks.BinaryPhaseBasisExtension
