module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! The structural row pass computes packed RHS words with ambient phases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Masked coupling operands depend only on the halo, including periodic
aliases. Values outside the packed source interval are never selected. -/
theorem couplingInputWords_halo_congr {s : ℕ} [NeZero s]
    (boundary : Bool) (t band a b i : ℕ) (C D : ZMod s → GaussianInt)
    (heq : ∀ j ∈ IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloVertices s a b,
      C j = D j) :
    couplingInputWords boundary t band a b i C = couplingInputWords boundary t band a b i D := by
  have hsub : (if boundary then IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloBoundary s t band a b
      else IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloInterior s t band a b) ⊆
      IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloVertices s a b := by
    split
    · exact Finset.sdiff_subset
    · exact IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloInterior_subset s t band a b
  unfold couplingInputWords
  apply List.map_congr_left
  intro δ hδ
  dsimp only
  apply ite_congr rfl
  · intro hj
    exact heq _ (hsub hj)
  · intro hj
    rfl

theorem couplingRowWords_packed {s : ℕ} [NeZero s] (P q t u band a b origin L : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) (hfit : origin+L ≤ s) :
    couplingRowWords P q t u band a b boundary C origin (packedInterval origin L B) =
      packedInterval origin L (couplingRowField P q t u band a b boundary C B) := by
  apply List.ext_getElem (by simp [packedInterval_length _ hfit])
  intro j hj hk
  have hjL : j < L := by simpa only [packedInterval_length _ hfit] using hk
  rw [couplingRowWords_getElem P q t u band a b origin boundary C
    (packedInterval origin L B) j (by simpa only [packedInterval_length _ hfit] using hjL),
    packedInterval_get B hfit hjL,packedInterval_get _ hfit hjL]
  simp only [couplingRowField,ZMod.val_natCast,Nat.mod_eq_of_lt (show origin+j < s by omega)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
