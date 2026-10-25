module

public import IntegerMultBounds.NLogN.PhaseCellGeneratedInterval
import Mathlib.Order.Interval.Finset.Nat

/-! Natural-arithmetic endpoints for the original ambient phase cells. These
formulas replace coordinate-set minima/maxima in the executable controller. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The least nonnegative coordinate whose phase is at least `phase`. -/
def phaseLower (s d phase : ℕ) : ℕ := (2*s*phase+2*d-1-s)/(2*d)

def naturalPhase (s t j : ℕ) : ℕ := (2*(t-s)*j+s)/(2*s)

theorem phaseIndex_nat {s t : ℕ} (hst : s ≤ t) (j : ℕ) :
    phaseIndex s t j = (naturalPhase s t j : ℤ) := by
  simp [phaseIndex, naturalPhase, Nat.cast_sub hst, Int.natCast_ediv]

theorem naturalPhase_monotone (s t : ℕ) : Monotone (naturalPhase s t) := by
  intro j k hjk
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left (2*(t-s)) hjk) s)

theorem phaseLower_le {s d phase j : ℕ} (hd : 0 < d) :
    phaseLower s d phase ≤ j ↔ 2*s*phase ≤ 2*d*j+s := by
  unfold phaseLower
  rw [Nat.div_le_iff_le_mul (by omega : 0 < 2*d), Nat.mul_comm j (2*d)]
  omega

theorem naturalPhase_eq_iff {s t phase j : ℕ} (hs : 0 < s) (hst : s < t) :
    naturalPhase s t j = phase ↔ phaseLower s (t-s) phase ≤ j ∧ j < phaseLower s (t-s) (phase+1) := by
  have lower (p : ℕ) : phaseLower s (t-s) p ≤ j ↔ p ≤ naturalPhase s t j := by
    rw [phaseLower_le (by omega), naturalPhase, Nat.le_div_iff_mul_le (by omega : 0 < 2*s)]
    constructor <;> intro h <;> nlinarith only [h]
  have hp := lower phase
  have hp' := lower (phase+1)
  omega

def naturalStart (s t w phase : ℕ) : ℕ := phaseLower s (t-s) phase+w

def naturalStop (s t w phase : ℕ) : ℕ := min s (phaseLower s (t-s) (phase+1))-w

def naturalLength (s t w phase : ℕ) : ℕ := naturalStop s t w phase-naturalStart s t w phase

theorem isInterior_nat {s t : ℕ} (hst : s ≤ t) (w j : ℕ) :
    isInterior s t w j = true ↔ w ≤ j ∧ j+w < s ∧ naturalPhase s t (j-w) = naturalPhase s t (j+w) := by
  by_cases hw : w ≤ j
  · have hleft : phaseIndex s t ((j : ℤ)-w) = (naturalPhase s t (j-w) : ℤ) := by
      rw [← Nat.cast_sub hw]
      exact phaseIndex_nat hst (j-w)
    have hright : phaseIndex s t ((j : ℤ)+w) = (naturalPhase s t (j+w) : ℤ) := by
      rw [← Nat.cast_add]
      exact phaseIndex_nat hst (j+w)
    simp [isInterior, hw, hleft, hright]
  · simp [isInterior, hw]

theorem interior_phase_iff_range {s t : ℕ} (hs : 0 < s) (hst : s < t) (w phase j : ℕ) :
    isInterior s t w j = true ∧ phaseIndex s t j = (phase : ℤ) ↔
      naturalStart s t w phase ≤ j ∧ j < naturalStop s t w phase := by
  rw [isInterior_nat hst.le, phaseIndex_nat hst.le]
  simp only [Int.natCast_inj]
  have hmono := naturalPhase_monotone s t
  have hleft := naturalPhase_eq_iff (phase := phase) (j := j-w) hs hst
  have hright := naturalPhase_eq_iff (phase := phase) (j := j+w) hs hst
  have hmid := naturalPhase_eq_iff (phase := phase) (j := j) hs hst
  have hlow := hmono (show j-w ≤ j by omega)
  have hhigh := hmono (show j ≤ j+w by omega)
  dsimp only [naturalStart, naturalStop]
  constructor
  · rintro ⟨⟨hw, hjs, hends⟩, hphase⟩
    have hl : naturalPhase s t (j-w) = phase := by omega
    have hr : naturalPhase s t (j+w) = phase := by omega
    obtain ⟨ha, _⟩ := hleft.mp hl
    obtain ⟨_, hb⟩ := hright.mp hr
    omega
  · rintro ⟨ha, hb⟩
    have hw : w ≤ j := by omega
    have hl := hleft.mpr (by omega)
    have hr := hright.mpr (by omega)
    exact ⟨⟨hw, by omega, hl.trans hr.symm⟩, hmid.mpr (by omega)⟩

theorem coordinateSet_eq_Ico {s t : ℕ} (hs : 0 < s) (hst : s < t) (w phase : ℕ) :
    coordinateSet s t w (phase : ℤ) = Finset.Ico (naturalStart s t w phase) (naturalStop s t w phase) := by
  ext j
  simp only [coordinateSet, interiorIndices, List.mem_toFinset, List.mem_filter, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq, Finset.mem_Ico]
  rw [interior_phase_iff_range hs hst]
  have hstop : naturalStop s t w phase ≤ s := (Nat.sub_le _ _).trans (min_le_left _ _)
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
