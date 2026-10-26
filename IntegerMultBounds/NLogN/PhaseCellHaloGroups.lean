module

public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys
import Mathlib.Data.List.GetD

/-! Equal-length groups of positive clipped cells retain the original ambient
phase order and discharge the solver's geometry contract. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

def haloLengthGroup (s t band a b L : ℕ) : List ℕ :=
  (List.range (t-s+1)).filter (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L))

theorem mem_haloLengthGroup (s t band a b L phase : ℕ) :
    phase ∈ haloLengthGroup s t band a b L ↔
      phase ≤ t-s ∧ 0 < L ∧ haloLength s t band a b phase = L := by
  simp [haloLengthGroup]

theorem haloLengthGroup_length_le (s t band a b L : ℕ) :
    (haloLengthGroup s t band a b L).length ≤ t-s+1 := by
  simpa only [haloLengthGroup,List.length_range] using List.length_filter_le
    (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L)) (List.range (t-s+1))

def haloGroupPhase (s t band a b L n : ℕ) : ℕ := (haloLengthGroup s t band a b L).getD n 0

def haloGroupOrigin (s t band a b L n : ℕ) : ZMod s :=
  (haloStart s t band a (haloGroupPhase s t band a b L n) : ℕ)

theorem haloGroupPhase_mem (s t band a b L : ℕ) (n : Fin (haloLengthGroup s t band a b L).length) :
    haloGroupPhase s t band a b L n ∈ haloLengthGroup s t band a b L := by
  unfold haloGroupPhase
  rw [List.getD_eq_getElem _ _ n.isLt]
  exact List.getElem_mem n.isLt

theorem haloGroupOrigin_val {s t : ℕ} [NeZero s] (band a b L : ℕ)
    (n : Fin (haloLengthGroup s t band a b L).length) :
    (haloGroupOrigin s t band a b L n).val = haloStart s t band a (haloGroupPhase s t band a b L n) := by
  obtain ⟨_,hL,hlen⟩ := (mem_haloLengthGroup s t band a b L _).mp (haloGroupPhase_mem s t band a b L n)
  have hstop := haloStop_le s t band b (haloGroupPhase s t band a b L n)
  apply ZMod.val_cast_of_lt
  dsimp only [haloLength] at hlen
  omega

theorem haloGroup_solver_geometry {s t : ℕ} [NeZero s] (hst : s < t) (band a b L : ℕ)
    (n : Fin (haloLengthGroup s t band a b L).length) :
    let lo := haloGroupOrigin s t band a b L n
    let I := haloInterior s t band a b
    0 < L ∧ lo.val+L ≤ s ∧
      (∀ i < L, Interior s t band (lo+(i : ZMod s)) ∧ lo+(i : ZMod s) ∈ I) ∧
      (∀ i < L, cell s t (lo+(i : ZMod s)) = cell s t lo) ∧
      ∀ j ∈ I, cell s t j = cell s t lo → ∃ i < L, lo+(i : ZMod s) = j := by
  obtain ⟨_,hL,hlen⟩ := (mem_haloLengthGroup s t band a b L _).mp (haloGroupPhase_mem s t band a b L n)
  have hh := halo_solver_geometry hst band a b (haloGroupPhase s t band a b L n) (by omega)
  simpa only [hlen,haloGroupOrigin] using hh

/-- The generated key list covers every clipped interior point through a group. -/
theorem haloGroups_cover {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (j : ZMod s) (hj : j ∈ haloInterior s t band a b) :
    ∃ L ∈ haloLengthKeys s t band a b, ∃ phase ∈ haloLengthGroup s t band a b L,
      haloStart s t band a phase ≤ j.val ∧ j.val < haloStop s t band b phase := by
  obtain ⟨phase,hphase,hstart,hstop⟩ := haloCells_cover hst band a b j hj
  have hk := haloLengthKeys_cover hst band a b phase hphase
  obtain ⟨hp,hpos⟩ := (mem_haloCellPhases s t band a b phase).mp hphase
  exact ⟨_,hk,phase,(mem_haloLengthGroup s t band a b _ phase).mpr ⟨hp,hpos,rfl⟩,hstart,hstop⟩

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
