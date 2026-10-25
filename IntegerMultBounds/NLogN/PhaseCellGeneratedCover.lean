module

public import IntegerMultBounds.NLogN.PhaseCellGeneratedInterval
public import Mathlib.Data.List.Dedup

/-! # A computed partition of the full ambient interior

One phase key is emitted for each nonempty interior interval. Interval geometry
comes from the computed endpoints; no interval cover is supplied as input.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

/-- Distinct nonempty phase keys, in order of last physical occurrence. -/
def activePhases (s t w : ℕ) : List ℤ :=
  (List.map (fun j : ℕ => phaseIndex s t j)
    (List.filter (isInterior s t w) (List.range s))).dedup

theorem mem_activePhases {s t : ℕ} [NeZero s] (w : ℕ) (phase : ℤ) :
    phase ∈ activePhases s t w ↔ ∃ j : ZMod s, Interior s t w j ∧ cell s t j = phase := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  simp only [activePhases, List.mem_dedup, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, ⟨hjs, hj⟩, hphase⟩
    have hval : (j : ZMod s).val = j := ZMod.val_cast_of_lt hjs
    refine ⟨(j : ZMod s), (isInterior_spec w _).mp (by simpa only [hval] using hj), ?_⟩
    simpa only [PhaseCellMatrix.cell, hval, phaseIndex_eq hs] using hphase
  · rintro ⟨j, hj, hphase⟩
    refine ⟨j.val, ⟨ZMod.val_lt j, (isInterior_spec w j).mpr hj⟩, ?_⟩
    simpa only [phaseIndex_eq hs, PhaseCellMatrix.cell] using hphase

theorem activePhases_nodup (s t w : ℕ) : (activePhases s t w).Nodup :=
  List.nodup_dedup _

/-- The number of nonempty interior cells is bounded by physical volume. -/
theorem activePhases_length_le (s t w : ℕ) : (activePhases s t w).length ≤ s := by
  unfold activePhases
  have hd := (List.dedup_sublist (List.map (fun j : ℕ => phaseIndex s t j)
    (List.filter (isInterior s t w) (List.range s)))).length_le
  have hf := List.length_filter_le (isInterior s t w) (List.range s)
  simp only [List.length_map, List.length_range] at hd hf
  exact hd.trans hf

/-- Every emitted key has the exact, nonwrapping interval geometry. -/
theorem activePhase_interval {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ)
    (phase : ℤ) (hphase : phase ∈ activePhases s t w) :
    let lo : ZMod s := (intervalStart s t w phase : ℕ)
    let L := intervalLength s t w phase
    0 < L ∧ lo.val + L ≤ s ∧ cell s t lo = phase ∧
      (∀ a < L, Interior s t w (lo + (a : ZMod s)) ∧ cell s t (lo + (a : ZMod s)) = cell s t lo) ∧
      ∀ j : ZMod s, (Interior s t w j ∧ cell s t j = phase) ↔ ∃ a < L, lo + (a : ZMod s) = j := by
  obtain ⟨k, hk⟩ := (mem_activePhases w phase).mp hphase
  exact generatedInterval_spec hst w phase k hk

/-- Every ambient interior coordinate belongs to a generated interval. -/
theorem generatedIntervals_cover {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ)
    (j : ZMod s) (hj : Interior s t w j) :
    ∃ phase ∈ activePhases s t w, ∃ a < intervalLength s t w phase,
      (intervalStart s t w phase : ZMod s) + (a : ZMod s) = j := by
  have hphase : cell s t j ∈ activePhases s t w := (mem_activePhases w _).mpr ⟨j, hj, rfl⟩
  obtain ⟨_, _, _, _, hcover⟩ := activePhase_interval hst w (cell s t j) hphase
  exact ⟨cell s t j, hphase, (hcover j).mp ⟨hj, rfl⟩⟩

/-- Distinct phase keys cannot publish the same physical coordinate. -/
theorem generatedIntervals_unique {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ)
    (phase₁ phase₂ : ℤ) (h₁ : phase₁ ∈ activePhases s t w) (h₂ : phase₂ ∈ activePhases s t w)
    (j : ZMod s)
    (hj₁ : ∃ a < intervalLength s t w phase₁, (intervalStart s t w phase₁ : ZMod s) + (a : ZMod s) = j)
    (hj₂ : ∃ a < intervalLength s t w phase₂, (intervalStart s t w phase₂ : ZMod s) + (a : ZMod s) = j) :
    phase₁ = phase₂ := by
  have hc₁ := (activePhase_interval hst w phase₁ h₁).2.2.2.2
  have hc₂ := (activePhase_interval hst w phase₂ h₂).2.2.2.2
  exact ((hc₁ j).mpr hj₁).2.symm.trans ((hc₂ j).mpr hj₂).2

/-- The generated ownership schedule covers exactly the computed interior. -/
theorem generatedIntervals_cover_iff {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) (j : ZMod s) :
    j ∈ interiorSet s t w ↔ ∃ phase ∈ activePhases s t w, ∃ a < intervalLength s t w phase,
      (intervalStart s t w phase : ZMod s) + (a : ZMod s) = j := by
  constructor
  · intro hj
    exact generatedIntervals_cover hst w j ((mem_interiorSet w j).mp hj)
  · rintro ⟨phase, hp, hj⟩
    have hcover := (activePhase_interval hst w phase hp).2.2.2.2
    exact (mem_interiorSet w j).mpr ((hcover j).mpr hj).1

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
