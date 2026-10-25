module

public import IntegerMultBounds.NLogN.PhaseCellNaturalEndpoints
import Mathlib.Data.List.GetD

/-! A bounded natural phase scan for equal-length groups. The schedule uses
only division, subtraction, comparison and filtering, and retains the exact
original ambient-cell geometry. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

def naturalLengthGroup (s t w L : ℕ) : List ℕ :=
  (List.range (t-s+1)).filter (fun phase => decide (0 < L ∧ naturalLength s t w phase = L))

theorem mem_naturalLengthGroup (s t w L phase : ℕ) :
    phase ∈ naturalLengthGroup s t w L ↔ phase ≤ t-s ∧ 0 < L ∧ naturalLength s t w phase = L := by
  simp [naturalLengthGroup]

theorem naturalLengthGroup_length_le (s t w L : ℕ) :
    (naturalLengthGroup s t w L).length ≤ t-s+1 := by
  simpa only [naturalLengthGroup, List.length_range] using List.length_filter_le
    (fun phase => decide (0 < L ∧ naturalLength s t w phase = L)) (List.range (t-s+1))

def naturalGroupPhase (s t w L n : ℕ) : ℕ := (naturalLengthGroup s t w L).getD n 0

def naturalGroupOrigin (s t w L n : ℕ) : ZMod s :=
  (naturalStart s t w (naturalGroupPhase s t w L n) : ℕ)

theorem naturalGroupPhase_mem (s t w L : ℕ) (n : Fin (naturalLengthGroup s t w L).length) :
    naturalGroupPhase s t w L n ∈ naturalLengthGroup s t w L := by
  unfold naturalGroupPhase
  rw [List.getD_eq_getElem _ _ n.isLt]
  exact List.getElem_mem n.isLt

theorem naturalGroupOrigin_val {s t : ℕ} [NeZero s] (w L : ℕ)
    (n : Fin (naturalLengthGroup s t w L).length) :
    (naturalGroupOrigin s t w L n).val = naturalStart s t w (naturalGroupPhase s t w L n) := by
  obtain ⟨_, hL, hlen⟩ := (mem_naturalLengthGroup s t w L _).mp (naturalGroupPhase_mem s t w L n)
  exact ZMod.val_cast_of_lt (naturalStart_lt w _ (by omega))

theorem naturalGroup_solver_geometry {s t : ℕ} [NeZero s] (hst : s < t) (w L : ℕ)
    (n : Fin (naturalLengthGroup s t w L).length) :
    let lo := naturalGroupOrigin s t w L n
    let I := interiorSet s t w
    0 < L ∧ lo.val+L ≤ s ∧
      (∀ a < L, Interior s t w (lo+(a : ZMod s)) ∧ lo+(a : ZMod s) ∈ I) ∧
      (∀ a < L, cell s t (lo+(a : ZMod s)) = cell s t lo) ∧
      ∀ j ∈ I, cell s t j = cell s t lo → ∃ a < L, lo+(a : ZMod s) = j := by
  let phase := naturalGroupPhase s t w L n
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  obtain ⟨_, hL, hlen⟩ := (mem_naturalLengthGroup s t w L phase).mp (naturalGroupPhase_mem s t w L n)
  have hpos : 0 < naturalLength s t w phase := by omega
  have ha := naturalStart_lt w phase hpos
  let k : ZMod s := (naturalStart s t w phase : ℕ)
  have hk : Interior s t w k ∧ cell s t k = (phase : ℤ) := by
    apply (mem_coordinateSet w (phase : ℤ) k).mp
    rw [show k.val = naturalStart s t w phase from ZMod.val_cast_of_lt ha,
      coordinateSet_eq_Ico hs hst]
    exact Finset.mem_Ico.mpr ⟨le_rfl, (naturalLength_pos_iff s t w phase).mp hpos⟩
  have hg := generatedInterval_solver_geometry hst w (phase : ℤ) k hk
  rw [intervalStart_eq_naturalStart hs hst w phase hpos, intervalLength_eq_naturalLength hs hst w phase,
    hlen] at hg
  exact hg

theorem naturalPhase_le_gap {s t : ℕ} (hs : 0 < s) {j : ℕ} (hj : j ≤ s) :
    naturalPhase s t j ≤ t-s := by
  have hh : naturalPhase s t j < t-s+1 := by
    rw [naturalPhase, Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)]
    have hm := Nat.mul_le_mul_left (2*(t-s)) hj
    nlinarith only [hm, hs]
  omega

/-- Every original interior vertex belongs to a selected natural phase. -/
theorem naturalGroups_cover {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ)
    (j : ZMod s) (hj : Interior s t w j) :
    ∃ L phase, phase ∈ naturalLengthGroup s t w L ∧
      naturalStart s t w phase ≤ j.val ∧ j.val < naturalStop s t w phase := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  let phase := naturalPhase s t j.val
  have hh := (interior_phase_iff_range hs hst w phase j.val).mp
    ⟨(isInterior_spec w j).mpr hj, phaseIndex_nat hst.le j.val⟩
  have hp : phase ≤ t-s := naturalPhase_le_gap hs (ZMod.val_lt j).le
  refine ⟨naturalLength s t w phase, phase, (mem_naturalLengthGroup s t w _ phase).mpr ?_, hh⟩
  exact ⟨hp, (naturalLength_pos_iff s t w phase).mpr (by omega), rfl⟩

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
