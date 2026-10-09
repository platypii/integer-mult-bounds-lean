import IntegerMultBounds.Machine.ActivePrefixCompactSwapBudget

/-! Two complete physical compact swaps surrounding a counted middle machine.
Each swap constructs and erases its own headers, and both joins are charged.
The special empty-middle roundtrip restores even arbitrarily dirty back bits. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactSwapRoundtrip
noncomputable section
open ActivePrefixCompactSwapData ActivePrefixCompactSwapRun
open CompactGadgetReservationShape
open Networks.Shared50ModularControl (prime)

abbrev count := 13+40+scratch

def roundtrip := seq ActivePrefixCompactSwapRun.program ActivePrefixCompactSwapRun.program
def sandwich {k : ℕ} (middle : Program count k prime) :=
  seq (seq ActivePrefixCompactSwapRun.program middle) ActivePrefixCompactSwapRun.program

variable (s : Shape) (n rows b : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool)
variable (hv : ∀ i, Counter.value (hs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
variable (hc : ∀ i, GrowingCounterData.Canonical (hs i))
variable (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hbp : 0<b)
variable (hr : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)

include hv hc hb cb hbp hr hK hd hg hp hw in
theorem roundtrip_runs (x : Array s rows (n*b)) :
    HoareTime roundtrip (fun v => v=bank (base hs bs x)) (fun v => v=bank (base hs bs x))
      (2*cost s rows (n*b)+1) := by
  have h₀ := runs s n rows b hs bs x hv hc hb cb hbp hr hK hd hg hp hw
  have h₁ := runs s n rows b hs bs (RadixRangePadding.transpose x) hv hc hb cb hbp hr hK hd hg hp hw
  rw [BinaryPackedFieldSwap.transpose_involutive] at h₁
  exact (h₀.seq h₁).consequence (fun _ h => h) (fun _ h => h) (by omega)

include hv hc hb cb hbp hr hK hd hg hp hw in
theorem sandwich_runs {k : ℕ} (middle : Program count k prime) (middleCost : ℕ)
    (x y : Array s rows (n*b))
    (hmid : HoareTime middle (fun v => v=bank (base hs bs (RadixRangePadding.transpose x)))
      (fun v => v=bank (base hs bs y)) middleCost) :
    HoareTime (sandwich middle) (fun v => v=bank (base hs bs x))
      (fun v => v=bank (base hs bs (RadixRangePadding.transpose y)))
      (2*cost s rows (n*b)+middleCost+2) := by
  have h₀ := runs s n rows b hs bs x hv hc hb cb hbp hr hK hd hg hp hw
  have h₁ := runs s n rows b hs bs y hv hc hb cb hbp hr hK hd hg hp hw
  exact ((h₀.seq hmid).seq h₁).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActivePrefixCompactSwapRoundtrip
