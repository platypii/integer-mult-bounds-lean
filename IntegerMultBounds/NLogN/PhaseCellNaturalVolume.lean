module

public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups
public import IntegerMultBounds.NLogN.PhaseCellGeneratedVolume

/-! The natural phase scan preserves exact interior volume. Each physical
coordinate contributes to exactly its computed natural phase fiber. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open scoped BigOperators

theorem naturalIntervals_volume {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ∑ phase ∈ Finset.range (t-s+1), naturalLength s t w phase = (interiorSet s t w).card := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hmaps : ∀ j ∈ physicalInterior s t w, naturalPhase s t j ∈ Finset.range (t-s+1) := by
    intro j hj
    exact Finset.mem_range.mpr (by
      have hh := naturalPhase_le_gap (t := t) hs (physicalInterior_lt s t w hj).le
      omega)
  have hcard (phase : ℕ) : ((physicalInterior s t w).filter (fun j => naturalPhase s t j = phase)).card =
      naturalLength s t w phase := by
    have hf : (physicalInterior s t w).filter (fun j => naturalPhase s t j = phase) =
        coordinateSet s t w (phase : ℤ) := by
      rw [coordinateSet_eq_filter]
      ext j
      simp only [Finset.mem_filter, phaseIndex_nat hst.le, Int.natCast_inj]
    rw [hf, coordinateSet_eq_Ico hs hst]
    simp [naturalLength]
  have hh := Finset.sum_fiberwise_of_maps_to' hmaps (fun _ : ℕ => (1 : ℕ))
  have hfib : ∑ phase ∈ Finset.range (t-s+1), naturalLength s t w phase = (physicalInterior s t w).card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one, hcard, Nat.cast_id] using hh
  exact hfib.trans (physicalInterior_card w)

theorem naturalIntervals_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ∑ phase ∈ Finset.range (t-s+1), naturalLength s t w phase ≤ s := by
  rw [naturalIntervals_volume hst w, ← physicalInterior_card w]
  have hc : (physicalInterior s t w).card ≤ (Finset.range s).card :=
    Finset.card_le_card (fun j hj => Finset.mem_range.mpr (physicalInterior_lt s t w hj))
  simpa using hc

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
