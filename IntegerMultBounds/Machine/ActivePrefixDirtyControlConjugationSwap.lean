import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationData

/-! Actual original-input T/back and U/back swaps on one full-array bank.
The complementary load workspace is stationary and blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationSwap
noncomputable section
open ActivePrefixDirtyControlConjugationData
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)

def count := 17+swapCount+65
def middleBank (v : Tapes 17 prime) := CleanSubbank.bank (s := swapCount) v
def bank (v : Tapes 17 prime) := CleanSubbank.bank (s := 65) (middleBank v)
def tProgram := extend (ActivePrefixCompactSwapPlaced.program swapFocus swap_injective) 65
def uProgram := extend (ActivePrefixDirtyControlUSwapPlaced.program swapFocus swap_injective) 65

variable (s : Shape) (n rows b : ℕ) (gs : Fin 7 → List Bool) (bw : List Bool)
variable (hs : Fin 6 → List Bool) (rs bs : List Bool)
variable (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
variable (gc : ∀ i, GrowingCounterData.Canonical (gs i))
variable (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
variable (hr : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)
include gv gc gb cb hbp hr hK hd hg hp hw

theorem t_runs (x : FullArray s rows) :
    HoareTime tProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (tSwap s rows (n*b) hw x)))
      (ActivePrefixCompactSwapRun.cost s rows (n*b)) := by
  let e := ActivePrefixCompactSwapData.volume_eq s rows (n*b) hw
  let y := view e.symm x
  have hsrc : SharedBank.payload (base gs bw hs rs bs y) swapFocus=ActivePrefixCompactSwapPlaced.sources gs bw y := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := ActivePrefixCompactSwapPlaced.runs (base gs bw hs rs bs y) swapFocus swap_injective
    s n rows b gs bw y hsrc gv gc gb cb hbp hr hK hd hg hp hw
  have he : ActivePrefixCompactSwapPlaced.result (base gs bw hs rs bs y) swapFocus y=
      base gs bw hs rs bs (RadixRangePadding.transpose y) := base_set _ _ _ _ _ _ _
  rw [he] at h
  have hi : base gs bw hs rs bs y=base gs bw hs rs bs x := base_view e.symm _ _ _ _ _ x
  have ho : base gs bw hs rs bs (RadixRangePadding.transpose y)=
      base gs bw hs rs bs (tSwap s rows (n*b) hw x) := (base_view e _ _ _ _ _ _).symm
  rw [hi,ho] at h
  exact hoare_extend_eq h (SharedBank.empty 65 prime)

theorem u_runs (x : FullArray s rows) :
    HoareTime uProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (uSwap s rows (n*b) hw x)))
      (ActivePrefixDirtyControlUSwapRun.cost s rows (n*b)) := by
  let e := ActivePrefixDirtyControlUSwapData.volume_eq s rows (n*b) hw
  let y := view e.symm x
  have hsrc : SharedBank.payload (base gs bw hs rs bs y) swapFocus=ActivePrefixDirtyControlUSwapPlaced.sources gs bw y := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := ActivePrefixDirtyControlUSwapPlaced.runs (base gs bw hs rs bs y) swapFocus swap_injective
    s n rows b gs bw y hsrc gv gc gb cb hbp hr hK hd hg hp hw
  have he : ActivePrefixDirtyControlUSwapPlaced.result (base gs bw hs rs bs y) swapFocus y=
      base gs bw hs rs bs (RadixRangePadding.transpose y) := base_set _ _ _ _ _ _ _
  rw [he] at h
  have hi : base gs bw hs rs bs y=base gs bw hs rs bs x := base_view e.symm _ _ _ _ _ x
  have ho : base gs bw hs rs bs (RadixRangePadding.transpose y)=
      base gs bw hs rs bs (uSwap s rows (n*b) hw x) := (base_view e _ _ _ _ _ _).symm
  rw [hi,ho] at h
  exact hoare_extend_eq h (SharedBank.empty 65 prime)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationSwap
