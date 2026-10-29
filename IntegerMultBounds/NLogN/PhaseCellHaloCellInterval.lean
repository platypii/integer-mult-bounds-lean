module

public import IntegerMultBounds.NLogN.PhaseCellHaloGeometry

/-! Generated clipped phase cells satisfy the interval solver's geometric
contract. The ambient phase is retained at artificial halo endpoints. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open PhaseCellMatrix

/-- A positive generated halo cell is a maximal interval of one ambient phase. -/
theorem haloCellInterval_spec {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b phase : ℕ) (hphase : phase ∈ haloCellPhases s t band a b) :
    let lo : ZMod s := (haloStart s t band a phase : ℕ)
    let L := haloLength s t band a b phase
    0 < L ∧ lo.val+L ≤ s ∧
      (∀ k < L, Interior s t band (lo+(k : ZMod s)) ∧ lo+(k : ZMod s) ∈ haloInterior s t band a b) ∧
      (∀ k < L, cell s t (lo+(k : ZMod s)) = cell s t lo) ∧
      (∀ j ∈ haloInterior s t band a b, cell s t j = cell s t lo →
        ∃ k < L, lo+(k : ZMod s) = j) := by
  exact halo_solver_geometry hst band a b phase ((mem_haloCellPhases _ _ _ _ _ _).mp hphase).2

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
