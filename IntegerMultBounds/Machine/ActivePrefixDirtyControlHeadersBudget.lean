import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersRun
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget

/-! Paid linear bounds for all three original-input dirty-control header
producers and their actual post-use cleanup, including arithmetic patches. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersBudget
open ActivePrefixLayoutHeadersData ActiveRepairRankHeadersCommands
open ActivePrefixDirtyControlHeadersData

 theorem patch_length (k : Kind) : (patch k).length≤7 := by cases k <;> decide

theorem values_le (k : Kind) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix (mode k) d≤A) :
    ∀ i, ActivePrefixDirtyControlHeadersData.values k d i≤6*A := by
  have hv := ActivePrefixLayoutHeadersBudget.values_le (mode k) d A hA ho hs
  have h10 := ho 10
  have h11 := ho 11
  change d.rho≤A at h10
  change d.sourceOffset≤A at h11
  intro i
  fin_cases i
  · exact hv 0
  · have h1 := hv 1
    change targetStart (mode k) d≤6*A at h1
    change startT k d≤6*A
    cases k <;> dsimp only [startT,mode] at h1 ⊢ <;> omega
  · have h0 := hv 0
    change prefixWidth (mode k) d≤6*A at h0
    change startU k d≤6*A
    unfold startU
    exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans h0)
  · exact hv 3
  · exact hv 4
  · exact hv 5
  · exact hv 6
  · exact hv 7
  · exact hv 8
  · exact hv 9

theorem finished_bounded (k : Kind) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix (mode k) d≤A) :
    Bounded (ActivePrefixDirtyControlHeadersData.finished k d) (6*A) := by
  intro i
  by_cases hi : i.val<14
  · simpa [ActivePrefixDirtyControlHeadersData.finished,hi] using (ho ⟨i.val,hi⟩).trans (by omega : A≤6*A)
  · by_cases hj : i.val<24
    · simpa [ActivePrefixDirtyControlHeadersData.finished,hi,hj] using values_le k d A hA ho hs ⟨i.val-14,by omega⟩
    · simp [ActivePrefixDirtyControlHeadersData.finished,hi,hj]

def constant := ActivePrefixLayoutHeadersBudget.constant+2100*3^7+1

theorem cost_bound (k : Kind) (d : Inputs) (A : ℕ) (hA : 0<A) (hp : 0<d.payload)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix (mode k) d≤A) :
    ActivePrefixDirtyControlHeadersRun.cost k d≤constant*A := by
  have hl := ActivePrefixLayoutHeadersBudget.cost_bound (mode k) d A hA hp ho hs
  have hpatch := scheduleCost_bounded (patch k) (ActivePrefixLayoutHeadersData.finished (mode k) d) (6*A)
    (ActivePrefixLayoutHeadersBudget.finished_bounded (mode k) d A hA ho hs)
  have hpw : 3^(patch k).length≤3^7 := Nat.pow_le_pow_right (by decide) (patch_length k)
  unfold ActivePrefixDirtyControlHeadersRun.cost constant
  nlinarith

def cleanupConstant := ActivePrefixLayoutHeadersBudget.cleanupConstant

theorem cleanup_bound (k : Kind) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix (mode k) d≤A) :
    ActivePrefixDirtyControlHeadersRun.cleanupCost k d≤cleanupConstant*A := by
  have h := scheduleCost_bounded outputCleanup (ActivePrefixDirtyControlHeadersData.finished k d) (6*A)
    (finished_bounded k d A hA ho hs)
  change ActivePrefixDirtyControlHeadersRun.cleanupCost k d≤300*3^10*(6*A+1) at h
  unfold cleanupConstant ActivePrefixLayoutHeadersBudget.cleanupConstant
  nlinarith

end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersBudget
