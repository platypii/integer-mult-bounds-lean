module

public import IntegerMultBounds.NLogN.PhaseCellGeneratedVolume
public import Mathlib.Data.List.GetD

/-! # Computed equal-length groups of ambient interior cells

Length is only the batching field; other setup-key parameters must still agree
before reuse. The grouping preserves exact processed volume.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open Finset
open scoped BigOperators

def lengthKeys (s t w : ℕ) : List ℕ :=
  (List.map (intervalLength s t w) (activePhases s t w)).dedup

def lengthGroup (s t w L : ℕ) : List ℤ :=
  List.filter (fun phase => decide (intervalLength s t w phase = L)) (activePhases s t w)

theorem mem_lengthKeys (s t w L : ℕ) :
    L ∈ lengthKeys s t w ↔ ∃ phase ∈ activePhases s t w, intervalLength s t w phase = L := by
  simp [lengthKeys]

theorem mem_lengthGroup (s t w L : ℕ) (phase : ℤ) :
    phase ∈ lengthGroup s t w L ↔ phase ∈ activePhases s t w ∧ intervalLength s t w phase = L := by
  simp [lengthGroup]

theorem lengthKeys_nodup (s t w : ℕ) : (lengthKeys s t w).Nodup := List.nodup_dedup _

theorem lengthGroup_nodup (s t w L : ℕ) : (lengthGroup s t w L).Nodup :=
  (activePhases_nodup s t w).filter _

theorem lengthKey_pos {s t : ℕ} [NeZero s] (hst : s < t) (w L : ℕ) (hL : L ∈ lengthKeys s t w) :
    0 < L := by
  obtain ⟨phase, hp, rfl⟩ := (mem_lengthKeys s t w L).mp hL
  exact (activePhase_interval hst w phase hp).1

theorem lengthGroup_pos (s t w L : ℕ) (hL : L ∈ lengthKeys s t w) :
    0 < (lengthGroup s t w L).length := by
  obtain ⟨phase, hp, hlen⟩ := (mem_lengthKeys s t w L).mp hL
  exact List.length_pos_of_mem ((mem_lengthGroup s t w L phase).mpr ⟨hp, hlen⟩)

theorem lengthGroup_toFinset (s t w L : ℕ) :
    (lengthGroup s t w L).toFinset = (activePhases s t w).toFinset.filter
      (fun phase => intervalLength s t w phase = L) := by
  ext phase
  simp [lengthGroup]

theorem lengthGroup_card (s t w L : ℕ) :
    ((activePhases s t w).toFinset.filter (fun phase => intervalLength s t w phase = L)).card =
      (lengthGroup s t w L).length := by
  rw [← lengthGroup_toFinset]
  exact List.toFinset_card_of_nodup (lengthGroup_nodup s t w L)

/-- Summing actual batch count times row length preserves interior volume. -/
theorem lengthGroups_volume {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ∑ L ∈ (lengthKeys s t w).toFinset, (lengthGroup s t w L).length * L = (interiorSet s t w).card := by
  have hmaps : ∀ phase ∈ (activePhases s t w).toFinset,
      intervalLength s t w phase ∈ (lengthKeys s t w).toFinset := by
    intro phase hp
    exact List.mem_toFinset.mpr ((mem_lengthKeys s t w _).mpr ⟨phase, List.mem_toFinset.mp hp, rfl⟩)
  have hsum := Finset.sum_fiberwise_of_maps_to' hmaps (fun L : ℕ => L)
  have hsum' : ∑ L ∈ (lengthKeys s t w).toFinset, (lengthGroup s t w L).length * L =
      ∑ phase ∈ (activePhases s t w).toFinset, intervalLength s t w phase := by
    simpa [Finset.sum_const, nsmul_eq_mul, lengthGroup_card] using hsum
  exact hsum'.trans ((sum_intervalLength hst w).trans (physicalInterior_card w))

/-- The executable key list, not merely its underlying set, has the same ledger. -/
theorem lengthGroups_list_volume {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ((lengthKeys s t w).map (fun L => (lengthGroup s t w L).length * L)).sum = (interiorSet s t w).card := by
  rw [← List.sum_toFinset _ (lengthKeys_nodup s t w)]
  exact lengthGroups_volume hst w

theorem lengthGroups_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) :
    ((lengthKeys s t w).map (fun L => (lengthGroup s t w L).length * L)).sum ≤ s := by
  rw [lengthGroups_list_volume hst w]
  have hh := activePhases_volume_le hst w
  rwa [activePhases_volume hst w] at hh

/-- Phase lookup for the ordinary natural-index row ABI; out-of-range values
are irrelevant to the bounded batch execution. -/
def groupPhase (s t w L n : ℕ) : ℤ := (lengthGroup s t w L).getD n 0

def groupOrigin (s t w L n : ℕ) : ZMod s :=
  (intervalStart s t w (groupPhase s t w L n) : ℕ)

theorem groupPhase_mem (s t w L : ℕ) (n : Fin (lengthGroup s t w L).length) :
    groupPhase s t w L n ∈ lengthGroup s t w L := by
  unfold groupPhase
  rw [List.getD_eq_getElem _ _ n.isLt]
  exact List.getElem_mem n.isLt

/-- Every row of the computed equal-length batch has the required full-cell
geometry in the original ambient interior mask. -/
theorem lengthGroup_solver_geometry {s t : ℕ} [NeZero s] (hst : s < t) (w L : ℕ)
    (n : Fin (lengthGroup s t w L).length) :
    let lo := groupOrigin s t w L n
    let I := interiorSet s t w
    0 < L ∧ lo.val + L ≤ s ∧
      (∀ a < L, PhaseCellMatrix.Interior s t w (lo + (a : ZMod s)) ∧ lo + (a : ZMod s) ∈ I) ∧
      (∀ a < L, PhaseCellMatrix.cell s t (lo + (a : ZMod s)) = PhaseCellMatrix.cell s t lo) ∧
      ∀ j ∈ I, PhaseCellMatrix.cell s t j = PhaseCellMatrix.cell s t lo →
        ∃ a < L, lo + (a : ZMod s) = j := by
  obtain ⟨hp, hlen⟩ := (mem_lengthGroup s t w L _).mp (groupPhase_mem s t w L n)
  obtain ⟨anchor, hk⟩ := (mem_activePhases w _).mp hp
  have hgeom := generatedInterval_solver_geometry hst w (groupPhase s t w L n) anchor hk
  simpa only [groupOrigin, hlen] using hgeom

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
