import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapData

/-! Physical construction, binary interchange and erasure of compact-U swap
geometry. The fixed forty-tape header workspace and the complete interchange
workspace both start and return blank, with every sequential join charged. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapRun
noncomputable section
open ActivePrefixDirtyControlUSwapData
open CompactGadgetReservationShape
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

abbrev scratch := BinaryRadixEqualShared.count
def bank (v : Tapes 13 prime) := BinaryRadixEqualShared.input (CleanSubbank.bank (s := 40) v)
def liftedFocus (i : Fin 4) : Fin (13+40) := Fin.castAdd 40 (swapFocus i)
def liftedPayload : Fin (13+40) := Fin.castAdd 40 (12 : Fin 13)

def setup := extend (CompactGadgetReservationHeadersCarvedPlacedRun.program (a := prime) headerFocus header_injective .temp) scratch
def swap := BinaryPackedFieldSwap.program liftedFocus liftedPayload
def cleanup := extend (extend (CompactGadgetReservationHeadersCarvedPlacedCleanup.program (a := prime) swapFocus) 40) scratch
def program := seq (seq setup swap) cleanup

def setupConstant := 31*CompactGadgetReservationHeadersCost.coefficient+82
def cost (s : Shape) (rows w : ℕ) := setupConstant*(rows*s.recordWidth)+
  BinaryRadixEqualShared.cost (P s rows) (G s w) (B s w) w (headerWords s rows w)+
  CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (headerWords s rows w)+2

theorem store_bank (v : Tapes 13 prime) (s : Shape) (rows w : ℕ) (x : Array s rows w) :
    BinaryPackedFieldSwap.store (CleanSubbank.bank (s := 40) v) liftedPayload x=
      CleanSubbank.bank (s := 40) (store v x) := by
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _

theorem setup_runs (s : Shape) (n rows b : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool)
    (x : Array s rows (n*b))
    (hv : ∀ i, Counter.value (hs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hbp : 0<b)
    (hr : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H) :
    HoareTime setup (fun v => v=bank (base hs bs x))
      (fun v => v=bank (headers (base hs bs x) s rows (n*b))) (setupConstant*(rows*s.recordWidth)) := by
  have h := CompactGadgetReservationHeadersCarvedPlacedRun.constructs_volume (base hs bs x)
    headerFocus header_injective hs bs s n rows b .temp (original_sources hs bs x)
    rfl rfl hv hc hb cb hbp hr hK hd hg hp hw
  exact hoare_extend_eq h (FixedHeaderBankCopy.empty scratch)

theorem swap_runs (s : Shape) (rows w : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool)
    (x : Array s rows w) (hr : 0<rows) (hp : 0<s.payload) :
    HoareTime swap (fun v => v=bank (headers (base hs bs x) s rows w))
      (fun v => v=bank (rotated (base hs bs x) s rows w x))
      (BinaryRadixEqualShared.cost (P s rows) (G s w) (B s w) w (headerWords s rows w)) := by
  have hsources := generated_headers (base hs bs x) s rows w
  have hsrc : BinaryAdjacentWidthHeadersShared.Sources
      (CleanSubbank.bank (s := 40) (headers (base hs bs x) s rows w)) liftedFocus (headerWords s rows w) := by
    constructor
    · intro i
      simpa only [liftedFocus,CleanSubbank.bank,Tapes.append,Fin.addCases_left] using hsources.tape i
    · intro i
      simpa only [liftedFocus,CleanSubbank.bank,Tapes.append,Fin.addCases_left] using hsources.head i
  have h := BinaryPackedFieldSwap.swaps (CleanSubbank.bank (s := 40) (headers (base hs bs x) s rows w))
    liftedFocus liftedPayload (P s rows) (G s w) (B s w) w (headerWords s rows w)
    (header_values s rows w) (header_canonical s rows w)
    (by unfold P Shape.prefixRange; positivity) (by unfold G CompactGadgetReservationHeadersCarvedData.gap; positivity)
    (by unfold B CompactGadgetReservationHeadersCarvedData.suffix; positivity) (by decide) hsrc x
  rw [store_bank _ s rows w x,store_headers,store_bank _ s rows w (RadixRangePadding.transpose x)] at h
  exact h

theorem cleared (s : Shape) (rows w : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool) (x : Array s rows w) :
    CompactGadgetReservationHeadersCarvedPlacedCleanup.cleared (rotated (base hs bs x) s rows w x) swapFocus=
      base hs bs (RadixRangePadding.transpose x) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleanup_runs (s : Shape) (rows w : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool) (x : Array s rows w) :
    HoareTime cleanup (fun v => v=bank (rotated (base hs bs x) s rows w x))
      (fun v => v=bank (base hs bs (RadixRangePadding.transpose x)))
      (CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (headerWords s rows w)) := by
  have hsources := BinaryPackedFieldSwap.store_sources (headers (base hs bs x) s rows w) swapFocus 12
    (headerWords s rows w) swap_ne (generated_headers _ s rows w) (RadixRangePadding.transpose x)
  have h := CompactGadgetReservationHeadersCarvedPlacedCleanup.cleans (rotated (base hs bs x) s rows w x)
    swapFocus swap_injective (headerWords s rows w) hsources.tape hsources.head
  rw [cleared] at h
  exact hoare_extend_eq (hoare_extend_eq h (SharedBank.empty 40 prime)) (FixedHeaderBankCopy.empty scratch)

theorem runs (s : Shape) (n rows b : ℕ) (hs : Fin 7 → List Bool) (bs : List Bool) (x : Array s rows (n*b))
    (hv : ∀ i, Counter.value (hs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hbp : 0<b)
    (hr : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H) :
    HoareTime program (fun v => v=bank (base hs bs x))
      (fun v => v=bank (base hs bs (RadixRangePadding.transpose x))) (cost s rows (n*b)) := by
  exact ((setup_runs s n rows b hs bs x hv hc hb cb hbp hr hK hd hg hp hw).seq
    (swap_runs s rows (n*b) hs bs x hr hp)).seq (cleanup_runs s rows (n*b) hs bs x) |>.consequence
      (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapRun
