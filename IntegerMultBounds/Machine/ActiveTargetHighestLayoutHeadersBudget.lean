import IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersRun
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget

/-! Paid linear bounds for deriving the highest-bit geometry from the same
original layout words used by the compact low-bit schedules. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersBudget
open ActivePrefixLayoutHeadersData (Inputs originalValues seeded)
open ActiveTargetHighestLayoutHeadersData
open ActiveRepairRankHeadersCommands

theorem schedule_length (mode : Mode) : (schedule mode).length≤21 := by
  cases mode <;> decide

theorem values_bound (mode : Mode) (d : Inputs) (A : ℕ)
    (ho : ∀ i,originalValues d i≤A) : ∀ i,values mode d i≤5*A := by
  have h0 := ho 0
  have h1 := ho 1
  have h2 := ho 2
  have h3 := ho 3
  have h4 := ho 4
  have h5 := ho 5
  have h10 := ho 10
  have h11 := ho 11
  have h12 := ho 12
  have h13 := ho 13
  simp [originalValues] at h0 h1 h2 h3 h4 h5 h10 h11 h12 h13
  intro i
  fin_cases i <;> cases mode
  all_goals simp [values,left,gap,suffix,baseWidth,sourceHigh]
  all_goals omega

theorem finished_bounded (mode : Mode) (d : Inputs) (A : ℕ)
    (ho : ∀ i,originalValues d i≤A) : Bounded (finished mode d) (5*A) := by
  intro i
  by_cases hi : i.val<14
  · simpa [finished,hi] using (ho ⟨i.val,hi⟩).trans (by omega : A≤5*A)
  · by_cases hj : i.val<19
    · simpa [finished,hi,hj] using values_bound mode d A ho ⟨i.val-14,by omega⟩
    · simp [finished,hi,hj]

def constant := 900*3^21+10
def cleanupConstant := 1800*3^5

theorem cost_bound (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i,originalValues d i≤A) :
    ActiveTargetHighestLayoutHeadersRun.cost mode d≤constant*A := by
  have h := scheduleCost_bounded (schedule mode) (seeded d) (A+1)
    (ActivePrefixLayoutHeadersBudget.seeded_bounded d A ho)
  have hp : 3^(schedule mode).length≤3^21 :=
    Nat.pow_le_pow_right (by decide) (schedule_length mode)
  unfold ActiveTargetHighestLayoutHeadersRun.cost constant
  nlinarith

theorem cleanup_bound (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i,originalValues d i≤A) :
    ActiveTargetHighestLayoutHeadersRun.cleanupCost mode d≤cleanupConstant*A := by
  have h := scheduleCost_bounded cleanup (finished mode d) (5*A) (finished_bounded mode d A ho)
  change ActiveTargetHighestLayoutHeadersRun.cleanupCost mode d≤300*3^5*(5*A+1) at h
  unfold cleanupConstant
  nlinarith

end IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersBudget
