import IntegerMultBounds.Machine.BinaryPackedFieldSwap
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedCleanup
import IntegerMultBounds.Machine.ActivePrefixLayoutSwap

/-! Literal compact-T/back interchange with original geometry descriptors.
Permanent ports are chunk/axes/global-guard/n/active/rows/payload/b, four blank
computed headers, and the full unchanged array. No P/G/B/width is supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactSwapData
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData (gap suffix)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

abbrev P (s : Shape) (rows : ℕ) := s.prefixRange rows .control
abbrev G (s : Shape) (w : ℕ) := gap s w .control
abbrev B (s : Shape) (w : ℕ) := suffix s w

abbrev volume (s : Shape) (rows w : ℕ) := RadixRangePadding.volume (P s rows) (2^w) (G s w) (B s w)
abbrev Array (s : Shape) (rows w : ℕ) := Fin (volume s rows w) → Bool

def headerFocus : Fin 12 → Fin 13 := ![0,1,2,3,4,5,6,8,9,10,11,7]
def swapFocus : Fin 4 → Fin 13 := ![9,10,11,8]
theorem header_injective : Function.Injective headerFocus := by decide
theorem swap_injective : Function.Injective swapFocus := by decide
theorem swap_ne : ∀ i, swapFocus i≠(12 : Fin 13) := by decide

def headerWords (s : Shape) (rows w : ℕ) :=
  CompactGadgetReservationHeadersCarvedRouting.headerWords s rows w .control

def base (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ} (x : Array s rows w) : Tapes 13 prime :=
  ⟨fun i => if i.val<8 then 1 else 0,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary bs
      else if i.val=12 then BinaryRadixRangePrepareAlphabet.word (fun j => bitSymbol (x j))
      else fun _ => blank⟩
def headers (v : Tapes 13 prime) (s : Shape) (rows w : ℕ) :=
  CompactGadgetReservationHeadersCarvedPlacedRun.result v headerFocus s rows w .control

def store (v : Tapes 13 prime) {s : Shape} {rows w : ℕ} (x : Array s rows w) :=
  BinaryPackedFieldSwap.store v 12 x

def rotated (v : Tapes 13 prime) (s : Shape) (rows w : ℕ) (x : Array s rows w) :=
  store (headers v s rows w) (RadixRangePadding.transpose x)

theorem original_sources (hs : Fin 7 → List Bool) (bs : List Bool)
    {s : Shape} {rows w : ℕ} (x : Array s rows w) :
    SharedBank.payload (base hs bs x) (CompactGadgetReservationHeadersCarvedPlacedRun.headerFocus headerFocus)=
      CompactGadgetReservationHeadersCarvedPlacedRun.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem generated_headers (v : Tapes 13 prime) (s : Shape) (rows w : ℕ) :
    BinaryAdjacentWidthHeadersShared.Sources (headers v s rows w) swapFocus (headerWords s rows w) := by
  obtain ⟨ht,hh⟩ := CompactGadgetReservationHeadersCarvedPlacedRun.result_headers v headerFocus header_injective s rows w .control
  constructor
  · intro i; fin_cases i; exact ht 0; exact ht 1; exact ht 2; exact ht 3
  · intro i; fin_cases i; exact hh 0; exact hh 1; exact hh 2; exact hh 3

theorem headers_store (v : Tapes 13 prime) (s : Shape) (rows w : ℕ) (x : Array s rows w) :
    headers (store v x) s rows w=store (headers v s rows w) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_store (hs : Fin 7 → List Bool) (bs : List Bool) {s : Shape} {rows w : ℕ}
    (x y : Array s rows w) : store (base hs bs x) y=base hs bs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem store_headers (hs : Fin 7 → List Bool) (bs : List Bool) (s : Shape) (rows w : ℕ)
    (x : Array s rows w) : store (headers (base hs bs x) s rows w) x=headers (base hs bs x) s rows w := by
  rw [←headers_store,base_store]

theorem header_values (s : Shape) (rows w : ℕ) :
    ∀ i, Counter.value (headerWords s rows w i)=BinaryRadixRangePrepare.values (P s rows) (G s w) (B s w) w i :=
  CompactGadgetReservationHeadersCarvedRouting.header_values s rows w .control

theorem header_canonical (s : Shape) (rows w : ℕ) :
    ∀ i, GrowingCounterData.Canonical (headerWords s rows w i) :=
  CompactGadgetReservationHeadersCarvedRouting.header_canonical s rows w .control

theorem volume_eq (s : Shape) (rows w : ℕ) (hw : w≤s.H) : volume s rows w=rows*s.recordWidth :=
  CompactGadgetReservationHeadersCarvedData.rectangle_volume s w rows hw .control

end
end IntegerMultBounds.Machine.ActivePrefixCompactSwapData
