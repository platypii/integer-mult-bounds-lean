module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryGatherSetup

/-! Pay generated class origins and final loop-count retirement once per class.
The existing geometry setup estimate already covers both native bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem selectedCyclicClassOriginSetup_le (cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) (V width radius L : ℕ),
    0 < width → V ≤ cV*Sizes.p m →
    preparedCoreOriginsCost V (Sizes.s m i) width radius L+
      (2*(coreGatherIndices (Sizes.s m i) width radius L).length+3) ≤ Sizes.T m ∧
    3*preparedCoreOriginsCost V (Sizes.s m i) width radius L ≤ Sizes.T m := by
  filter_upwards [selectedGeometryGatherSetup_le cV] with m hsetup
  intro h i V width radius L hw hV
  obtain ⟨ht,hs⟩ := hsetup h i V width radius L hw hV
  have hmul : 6*(coreGatherIndices (Sizes.s m i) width radius L).length ≤
      (coreGatherIndices (Sizes.s m i) width radius L).length*(8*V+6) := by nlinarith
  have hretire : 2*(coreGatherIndices (Sizes.s m i) width radius L).length+3 ≤
      preparedCoreOriginsCost V (Sizes.s m i) width radius L := by
    unfold preparedCoreOriginsCost
    omega
  constructor <;> omega

end IntegerMultBounds.MathlibTM2.Cost
