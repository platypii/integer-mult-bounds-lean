import IntegerMultBounds.Machine.CompactComplexScalarGrid
import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry

/-! Numerator growth from scalar network levels and actual butterfly depths
has an explicit signed-width budget. Geometric Visits derive the maximum
remaining recursion exponent from the original active-axis header. These
lemmas do not assert an assembled recursive execution theorem. -/
namespace IntegerMultBounds.Machine.CompactRecursiveGridBudget
noncomputable section
open CompactComplexRecursiveGeometry

def bound (p C levels butterflies : ℕ) := 2^p*C^levels*4^butterflies

def halfWidth (p C levels butterflies : ℕ) :=
  p+levels*Nat.clog 2 (C+1)+2*butterflies+1

theorem scalar_step (p C levels butterflies : ℕ) :
    bound p C levels butterflies*C=bound p C (levels+1) butterflies := by
  unfold bound
  rw [pow_succ]
  ring

theorem butterfly_step (p C levels butterflies : ℕ) :
    4*bound p C levels butterflies=bound p C levels (butterflies+1) := by
  unfold bound
  rw [pow_succ]
  ring

theorem strict (p C levels butterflies : ℕ) :
    bound p C levels butterflies<2^(halfWidth p C levels butterflies) := by
  have hc : C≤2^(Nat.clog 2 (C+1)) := (Nat.le_succ C).trans
    (Nat.le_pow_clog (by decide : 1<2) (C+1))
  have hp := Nat.pow_le_pow_left hc levels
  have hbase : 4^butterflies=2^(2*butterflies) := by
    rw [show (4:ℕ)=2^2 by decide,pow_mul]
  have hb : bound p C levels butterflies≤2^(p+levels*Nat.clog 2 (C+1)+2*butterflies) := by
    unfold bound
    rw [←pow_mul,Nat.mul_comm (Nat.clog 2 (C+1)) levels] at hp
    rw [hbase]
    rw [pow_add,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
  exact hb.trans_lt (Nat.pow_lt_pow_right (by decide) (by unfold halfWidth; omega))

theorem visit_remaining_depth {active left k : ℕ} (v : Visit active left k) :
    k≤Nat.log arity active :=
  Nat.le_log_of_pow_le (by decide : 1<arity) (by have := v.fits; omega)

/-- The budget reserves one fixed scalar growth factor per inherited network
level and two growth bits per genuine butterfly dependency. -/
theorem width_linear (p C levels butterflies D : ℕ) (hlevels : levels≤D) (hbutterflies : butterflies≤D) :
    halfWidth p C levels butterflies≤p+(Nat.clog 2 (C+1)+2)*D+1 := by
  have h := Nat.mul_le_mul_right (Nat.clog 2 (C+1)) hlevels
  unfold halfWidth
  nlinarith

end
end IntegerMultBounds.Machine.CompactRecursiveGridBudget
