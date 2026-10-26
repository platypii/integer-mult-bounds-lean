module

public import IntegerMultBounds.NLogN.PhaseCellHaloGeometry
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The generated clipped intervals partition the selected halo interior
exactly. Empty phases contribute zero volume and disappear from the schedule. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix
open scoped BigOperators

theorem haloPhase_card {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ) :
    ((haloInterior s t band a b).filter (fun j => naturalPhase s t j.val = phase)).card =
      haloLength s t band a b phase := by
  have hh : ((haloInterior s t band a b).filter (fun j => naturalPhase s t j.val = phase)).card =
      (Finset.Ico (haloStart s t band a phase) (haloStop s t band b phase)).card := by
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      obtain ⟨hI,hphase⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_Ico.mpr
      apply (haloInterior_phase_iff hst band a b phase j).mp
      exact ⟨hI,(cell_eq_naturalPhase hst j).trans (by rw [hphase])⟩
    · intro j hj k hk he
      exact ZMod.val_injective s he
    · intro j hj
      obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hj
      have hjs : j < s := hb.trans_le (haloStop_le s t band b phase)
      have hv : (j : ZMod s).val = j := ZMod.val_cast_of_lt hjs
      obtain ⟨hI,hphase⟩ := (haloInterior_phase_iff hst band a b phase (j : ZMod s)).mpr
        (by simpa only [hv] using And.intro ha hb)
      refine ⟨(j : ZMod s),Finset.mem_filter.mpr ⟨hI,?_⟩,hv⟩
      exact Int.natCast_inj.mp ((cell_eq_naturalPhase hst (j : ZMod s)).symm.trans hphase)
  simpa only [Nat.card_Ico,haloLength] using hh

theorem haloIntervals_volume {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    ∑ phase ∈ Finset.range (t-s+1), haloLength s t band a b phase = (haloInterior s t band a b).card := by
  have hmaps : ∀ j ∈ haloInterior s t band a b, naturalPhase s t j.val ∈ Finset.range (t-s+1) := by
    intro j _
    exact Finset.mem_range.mpr (by have hh := naturalPhase_le_gap (t := t) (NeZero.pos s) (ZMod.val_lt j).le; omega)
  have hh := Finset.sum_fiberwise_of_maps_to' hmaps (fun _ : ℕ => (1 : ℕ))
  simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,haloPhase_card hst band a b] using hh

/-- The executable positive-phase list has the same exact volume as the full scan. -/
theorem haloCellPhases_volume {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    ((haloCellPhases s t band a b).map (haloLength s t band a b)).sum =
      (haloInterior s t band a b).card := by
  have hfilter (xs : List ℕ) :
      ((xs.filter (fun phase => decide (0 < haloLength s t band a b phase))).map
        (haloLength s t band a b)).sum = (xs.map (haloLength s t band a b)).sum := by
    induction xs with
    | nil => simp
    | cons phase xs ih =>
      by_cases hp : 0 < haloLength s t band a b phase
      · simp [hp,ih]
      · have hz : haloLength s t band a b phase = 0 := by omega
        simp [hz,ih]
  rw [haloCellPhases,hfilter,← List.sum_toFinset _ (List.nodup_range (n := t-s+1))]
  have hrange : (List.range (t-s+1)).toFinset = Finset.range (t-s+1) := by ext phase; simp
  rw [hrange]
  exact haloIntervals_volume hst band a b

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
