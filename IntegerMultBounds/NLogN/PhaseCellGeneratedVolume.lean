module

public import IntegerMultBounds.NLogN.PhaseCellGeneratedCover
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Volume accounting for the computed full-interior partition -/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open Finset PhaseCellMatrix
open scoped BigOperators

/-- Physical interior coordinates before phase grouping. -/
def physicalInterior (s t w : ℕ) : Finset ℕ :=
  (List.filter (isInterior s t w) (List.range s)).toFinset

theorem coordinateSet_eq_filter (s t w : ℕ) (phase : ℤ) :
    coordinateSet s t w phase = (physicalInterior s t w).filter (fun j : ℕ => phaseIndex s t j = phase) := by
  ext j
  simp [coordinateSet, interiorIndices, physicalInterior, Bool.and_eq_true, and_assoc]

theorem activePhases_toFinset (s t w : ℕ) :
    (activePhases s t w).toFinset = (physicalInterior s t w).image (fun j : ℕ => phaseIndex s t j) := by
  ext phase
  simp [activePhases, physicalInterior]

theorem physicalInterior_lt (s t w : ℕ) {j : ℕ} (hj : j ∈ physicalInterior s t w) : j < s :=
  List.mem_range.mp (List.mem_of_mem_filter (List.mem_toFinset.mp hj))

theorem interiorSet_eq_image (s t w : ℕ) :
    interiorSet s t w = (physicalInterior s t w).image (fun j : ℕ => (j : ZMod s)) := by
  ext j
  simp [interiorSet, physicalInterior]

theorem physicalInterior_card {s t : ℕ} [NeZero s] (w : ℕ) :
    (physicalInterior s t w).card = (interiorSet s t w).card := by
  rw [interiorSet_eq_image]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hav : (a : ZMod s).val = a := ZMod.val_cast_of_lt (physicalInterior_lt s t w ha)
  have hbv : (b : ZMod s).val = b := ZMod.val_cast_of_lt (physicalInterior_lt s t w hb)
  simpa only [hav, hbv] using congrArg ZMod.val hab

/-- Convexity makes the computed span length exactly its number of vertices. -/
theorem intervalLength_eq_card {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) (phase : ℤ) :
    intervalLength s t w phase = (coordinateSet s t w phase).card := by
  let N := coordinateSet s t w phase
  by_cases hn : N.Nonempty
  · obtain ⟨k, hkN⟩ := hn
    have hn : N.Nonempty := ⟨k, hkN⟩
    have hks : k < s := coordinateSet_lt s t w phase hkN
    have hk : Interior s t w (k : ZMod s) ∧ cell s t (k : ZMod s) = phase :=
      (mem_coordinateSet w phase (k : ZMod s)).mp (by simpa only [ZMod.val_cast_of_lt hks] using hkN)
    let a := N.min' hn
    let b := N.max' hn
    have haN : a ∈ N := min'_mem N hn
    have hbN : b ∈ N := max'_mem N hn
    have hab : a ≤ b := min'_le N b hbN
    have hbs : b < s := coordinateSet_lt s t w phase hbN
    have hstart : intervalStart s t w phase = a := by simp [intervalStart, N, hn, a]
    have hlength : intervalLength s t w phase = b - a + 1 := by simp [intervalLength, N, hn, a, b]
    have hs := generatedInterval_spec hst w phase (k : ZMod s) hk
    dsimp only at hs
    rw [hstart, hlength] at hs
    obtain ⟨_, _, hphase, hcover, _⟩ := hs
    have heq : N = Icc a b := by
      ext j
      constructor
      · intro hj
        exact mem_Icc.mpr ⟨min'_le N j hj, le_max' N j hj⟩
      · intro hj
        obtain ⟨haj, hjb⟩ := mem_Icc.mp hj
        have hjs : j < s := by omega
        have hjval : (j : ZMod s).val = j := ZMod.val_cast_of_lt hjs
        have hrepr : (a : ZMod s) + ((j - a : ℕ) : ZMod s) = (j : ZMod s) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le haj]
        have hh := hcover (j - a) (by omega)
        rw [hrepr] at hh
        have hm := (mem_coordinateSet w phase (j : ZMod s)).mpr ⟨hh.1, hh.2.trans hphase⟩
        simpa only [hjval] using hm
    rw [hlength]
    change b - a + 1 = N.card
    rw [heq, Nat.card_Icc]
    omega
  · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [intervalLength, N, he]

/-- The sum over generated keys is exactly the physical interior volume. -/
theorem sum_intervalLength {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ∑ phase ∈ (activePhases s t w).toFinset, intervalLength s t w phase = (physicalInterior s t w).card := by
  simp_rw [intervalLength_eq_card hst w, coordinateSet_eq_filter]
  rw [activePhases_toFinset]
  exact (Finset.card_eq_sum_card_image (fun j : ℕ => phaseIndex s t j) (physicalInterior s t w)).symm

/-- Grouping by phase never increases processed interior volume. -/
theorem sum_intervalLength_le {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ∑ phase ∈ (activePhases s t w).toFinset, intervalLength s t w phase ≤ s := by
  rw [sum_intervalLength hst w]
  have hsub : physicalInterior s t w ⊆ Finset.range s := by
    intro j hj
    exact Finset.mem_range.mpr (physicalInterior_lt s t w hj)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

/-- The actual duplicate-free key list processes every interior vertex once. -/
theorem activePhases_volume {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ((activePhases s t w).map (intervalLength s t w)).sum = (interiorSet s t w).card := by
  rw [← List.sum_toFinset _ (activePhases_nodup s t w), sum_intervalLength hst w, physicalInterior_card]

theorem activePhases_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ((activePhases s t w).map (intervalLength s t w)).sum ≤ s := by
  rw [← List.sum_toFinset _ (activePhases_nodup s t w)]
  exact sum_intervalLength_le hst w

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
