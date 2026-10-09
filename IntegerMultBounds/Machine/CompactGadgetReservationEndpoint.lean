import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Complete physical per-role compact load from the actual reservation
endpoint, with original shape/offset tapes explicit and all other roles framed. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationEndpoint
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount roleSlot)
open CompactGadgetReservationPlacement (CommonTapes NativeTapes commonSlots)
variable {c r : ℕ}

def common (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) : Tapes (CommonTapes c) prime :=
  (CompactRowReservationEndpoint.final (a := prime) hc x rs ls).append originals

def localCaller (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) (j : Fin c) :=
  SharedBank.payload (common hc s x rs ls originals) (commonSlots c j)

def before (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) :=
  CleanSubbank.bank (s := NativeTapes) (common hc s x rs ls originals)

def after (hc : 0 < c) (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool)
    (originals : Tapes 5 prime) (j : Fin c) (V : List Bool) :=
  CleanSubbank.bank (s := NativeTapes)
    (SharedPlacementAlphabet.setTape (common hc s x rs ls originals) (commonSlots c j 5)
      (BinaryRadixRangePrepareAlphabet.word
        (fun i => bitSymbol (CompactGadgetReservationRun.output s n hn f hc x j V i))) 0)

def source (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) :=
  CleanSubbank.bank (s := NativeTapes)
    ((CompactRowReservationPlacement.bank (CompactRowReservationData.original x)
      (CompactRowReservationRun.emptyPayload (c := c)) rs ls none none).append originals)

def reserveAndLoad (ha : 2 ≤ prime) (c : ℕ) (j : Fin c) :=
  seq (extend (extend (CompactRowReservationRun.program ha c) 5) NativeTapes)
    (CompactGadgetReservationPlacement.program c j)

/-- One fixed physical load on the chosen reserved temp/control field, from
the padded role word produced by the original-row-header reservation machine.
Original shape/offset inputs are supplied physically; their construction is
separate. Other roles, original row/width headers and all private areas survive. -/
theorem runs (hc : 0 < c) (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool) (originals : Tapes 5 prime)
    (j : Fin c) (hr : 0 < r) (hp : 0 < s.payload) (V : List Bool)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n)
    (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values
      (s.prefixRange (rowCount r c) f) (s.gap n f) (s.suffix n) (s.width n) i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsrc : BinaryAdjacentWidthHeadersShared.Sources (localCaller hc s x rs ls originals j)
      BinaryPackedOffsetOriginalRun.headers hs)
    (htV : (localCaller hc s x rs ls originals j).tape 4 =
      putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank)) 0 (V.map bitSymbol))
    (hhV : (localCaller hc s x rs ls originals j).head 4 = 0) :
    HoareTime (CompactGadgetReservationPlacement.program c j)
      (fun v => v = before hc s x rs ls originals)
      (fun v => v = after hc s n hn f x rs ls originals j V)
      (BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
        (s.width n) (s.gap n f) (s.suffix n) hs) := by
  have hrole := CompactGadgetReservationPlacement.projected_role hc s x rs ls originals j
  have hrun := CompactGadgetReservationRun.runs (localCaller hc s x rs ls originals j)
    s n hn f hc x rs ls j (CompactGadgetReservationData.rowCount_pos hc hr) hp V hV hs hv
    hcan hsrc htV hhV hrole.2 hrole.1
  exact CompactGadgetReservationPlacement.realizes j (common hc s x rs ls originals) _ _ hrun

/-- Actual padding, row splitting and reserved-role load in sequence. The
load contract is furnished by `runs`; originals/private blanks are framed
through the real reservation program, with all joins and setup charged. -/
theorem reserve_then_load (ha : 2 ≤ prime) (hc : 0 < c) (s : Shape) (n : ℕ)
    (hn : n ≤ s.axes) (f : Front) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) (j : Fin c) (V : List Bool) (C : ℕ)
    (hvR : Counter.value rs = r) (hvL : Counter.value ls = s.recordWidth)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hr : 0 < r) (hp : 0 < s.payload)
    (hload : HoareTime (CompactGadgetReservationPlacement.program c j)
      (fun v => v = before hc s x rs ls originals)
      (fun v => v = after hc s n hn f x rs ls originals j V) C) :
    HoareTime (reserveAndLoad ha c j)
      (fun v => v = source (c := c) s x rs ls originals)
      (fun v => v = after hc s n hn f x rs ls originals j V)
      ((CompactRowReservationBudget.constant c*(c+1))*(r*s.recordWidth)+1+C) := by
  have hl : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hreserve := hoare_extend_eq (hoare_extend_eq
    (CompactRowReservationBudget.runs ha c rs ls r s.recordWidth x hvR hvL cr cl hr hl hc)
    originals) (SharedBank.empty NativeTapes prime)
  exact hreserve.seq hload

end
end IntegerMultBounds.Machine.CompactGadgetReservationEndpoint
