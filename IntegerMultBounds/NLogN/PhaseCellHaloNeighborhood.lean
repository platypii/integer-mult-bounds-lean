module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryCount
public import IntegerMultBounds.NLogN.PhaseCellSpatialCouplingOffsets
public import IntegerMultBounds.NLogN.PhaseCellIntervals

/-! An enlarged interior protects the entire coupling stencil from the halo boundary. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

variable {s t : ℕ} [NeZero s]

/-- Shrinking the guard band by radius admits every offset of that radius.
The ambient phase and the artificial halo endpoints are both retained. -/
theorem haloInterior_shift (hst : s ≤ t) (band radius a b : ℕ) (i : ZMod s)
    (hi : i ∈ haloInterior s t (band+radius) a b) (δ : ℤ)
    (hδ : -(radius : ℤ) ≤ δ ∧ δ ≤ radius) :
    i+(δ : ZMod s) ∈ haloInterior s t band a b := by
  obtain ⟨hiI,ha,hb⟩ := Finset.mem_filter.mp hi
  obtain ⟨hlo,hhi,hphase⟩ := (mem_interiorSet _ i).mp hiI
  let j := i+(δ : ZMod s)
  have hjval : (j.val : ℤ) = (i.val : ℤ)+δ := by
    have hj : j = (((i.val : ℤ)+δ : ℤ) : ZMod s) := by simp [j]
    rw [hj,ZMod.val_intCast,Int.emod_eq_of_lt (by omega) (by omega)]
  have hleft := PhaseCellIntervals.phase_eq_of_between (NeZero.pos s) hst
    (j := (i.val : ℤ)-(band+radius)) (k := (i.val : ℤ)+(band+radius))
    (l := (j.val : ℤ)-band) (by omega) (by omega) hphase
  have hright := PhaseCellIntervals.phase_eq_of_between (NeZero.pos s) hst
    (j := (i.val : ℤ)-(band+radius)) (k := (i.val : ℤ)+(band+radius))
    (l := (j.val : ℤ)+band) (by omega) (by omega) hphase
  change j ∈ haloInterior s t band a b
  apply Finset.mem_filter.mpr
  refine ⟨(mem_interiorSet band j).mpr ⟨by omega,by omega,hleft.trans hright.symm⟩,by omega,by omega⟩

theorem spatialCouplingOffsets_bounds (band : ℕ) {δ : ℤ}
    (hδ : δ ∈ spatialCouplingOffsets band) : -(band : ℤ) ≤ δ ∧ δ ≤ band := by
  rw [spatialCouplingOffsets_eq_range] at hδ
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hδ
  have hn' := List.mem_range.mp hn
  omega

theorem haloInterior_stencil_disjoint_boundary (hst : s ≤ t) (band a b : ℕ) (i : ZMod s)
    (hi : i ∈ haloInterior s t (2*band) a b) {δ : ℤ} (hδ : δ ∈ spatialCouplingOffsets band) :
    i+(δ : ZMod s) ∉ haloBoundary s t band a b := by
  have hnear := haloInterior_shift hst band band a b i (by simpa [two_mul] using hi) δ
    (spatialCouplingOffsets_bounds band hδ)
  exact fun h => (Finset.mem_sdiff.mp h).2 hnear

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
