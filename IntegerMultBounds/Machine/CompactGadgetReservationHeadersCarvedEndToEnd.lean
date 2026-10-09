import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReservationRouting

/-! Original physical array through padding, role splitting, erased reservation
work, original-row/packing-width header synthesis, and the actual carved load.
The offset stream remains a physical explicit input; no derived descriptor or
execution callback is supplied. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedEndToEnd
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationData (rowCount)
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationPlacement (ReservationTapes NativeTapes)
variable {c r : ℕ}

def reserveProgram (ha : 2 ≤ prime) (c : ℕ) :=
  CompactGadgetReservationHeadersCarvedReservationRouting.program
    (CompactRowReservationRun.program ha c) 25 1 1 15 NativeTapes
def program (ha : 2 ≤ prime) (c : ℕ) (j : Fin c) (f : Front) :=
  seq (reserveProgram ha c) (CompactGadgetReservationHeadersCarvedReserved.program c j f)
def source (hs : Fin 6 → List Bool) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls bs V : List Bool) :=
  CompactGadgetReservationHeadersCarvedReservationRouting.bank (w₁ := 15) (w₂ := NativeTapes)
    (CompactGadgetReservationHeadersWords.common (a := prime) (CompactGadgetReservationHeadersCaller.words hs))
    (CompactRowReservationPlacement.bank (CompactRowReservationData.original x)
      (CompactRowReservationRun.emptyPayload (c := c)) rs ls none none)
    (CompactGadgetReservationHeadersReserved.offsets V)
    (CompactGadgetReservationHeadersCarvedReserved.packing bs)
def loadCost (hs : Fin 6 → List Bool) (s : Shape) (n b r c : ℕ) (f : Front) :=
  CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+
    CompactGadgetReservationHeadersCarvedCaller.headerCost hs r c (n*b) f+1+
    BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f) (n*b)
      (gap s (n*b) f) (suffix s (n*b))
      (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f)
def cost (hs : Fin 6 → List Bool) (s : Shape) (n b r c : ℕ) (f : Front) :=
  CompactRowReservationRun.budget c r s.recordWidth+1+loadCost hs s n b r c f

theorem runs (ha : 2 ≤ prime) (hc : 0 < c) (s : Shape) (n b : ℕ)
    (hn : n ≤ s.axes) (hb : b ≤ s.guard) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls bs : List Bool) (j : Fin c) (V : List Bool)
    (hs : Fin 6 → List Bool)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) (hr : 0 < r)
    (hvL : Counter.value ls = s.recordWidth) (cl : GrowingCounterData.Canonical ls)
    (hvB : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) (hbpos : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersCaller.originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hp : 0 < s.payload)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (n*b) (gap s (n*b) f)*(n*b)) :
    HoareTime (program ha c j f)
      (fun v => v = source (c := c) hs s x rs ls bs V)
      (fun v => v = CleanSubbank.bank (s := NativeTapes)
        (BinaryPackedOffsetOriginalPlaced.store
          (CompactGadgetReservationHeadersCarvedCaller.prepared hs s n r c (n*b) f
            (CompactGadgetReservationHeadersCarvedReserved.spectators hc s x rs ls bs V))
          (CompactGadgetReservationHeadersCaller.actionFocus
            (CompactGadgetReservationHeadersCarvedReserved.Vslot c)
            (CompactGadgetReservationHeadersCarvedReserved.Xslot c j))
          (CompactGadgetReservationHeadersCarvedReserved.output hc s n b
            (packed_width_le s n b hn hb) f x j V)))
      (cost hs s n b r c f) := by
  have hrec : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hreserve := CompactGadgetReservationHeadersCarvedReservationRouting.realizes (w₁ := 15) (w₂ := NativeTapes)
    (CompactRowReservationRun.program ha c)
    (CompactGadgetReservationHeadersWords.common (a := prime) (CompactGadgetReservationHeadersCaller.words hs))
    (CompactRowReservationPlacement.bank (CompactRowReservationData.original x)
      (CompactRowReservationRun.emptyPayload (c := c)) rs ls none none)
    (CompactRowReservationEndpoint.final (a := prime) hc x rs ls)
    (CompactGadgetReservationHeadersReserved.offsets V)
    (CompactGadgetReservationHeadersCarvedReserved.packing bs) _
    (CompactRowReservationRun.runs ha c rs ls r s.recordWidth x hvR hvL cr cl hr hrec hc)
  have hload := CompactGadgetReservationHeadersCarvedReserved.runs hc s n b hn hb f x rs ls bs j V hs
    hvR cr hr hvB cb hbpos hv hcan hK hd hG hp hV
  exact hreserve.seq hload

theorem reservation_bound (s : Shape) (r c : ℕ) (hr : 0 < r) (hc : 0 < c) (hp : 0 < s.payload) :
    CompactRowReservationRun.budget c r s.recordWidth+1 ≤
      (CompactRowReservationBudget.constant c*c+1)*(rowCount r c*s.recordWidth) := by
  have hrec : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hrows := CompactGadgetReservationData.rowCount_pos hc hr
  have hb := CompactRowReservationBudget.linear c r s.recordWidth hc hr hrec
  have he := Nat.div_mul_cancel (CompactRowPaddingRound.padded_bounds r c hc).2.2
  change rowCount r c*c = IntegerMultBounds.Compact.Layout.paddedRows r c at he
  have hV := Nat.mul_pos hrows hrec
  nlinarith

theorem uniform_bound (c : ℕ) (hc : 0 < c) : ∃ C : ℝ, 0 < C ∧
    ∀ (hs : Fin 6 → List Bool) (s : Shape) (n b r : ℕ) (f : Front),
    0 < r → 0 < s.chunk → 0 < s.axes → 0 < s.guard → 0 < s.payload → n*b ≤ s.H →
    (∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersCaller.originals s n i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost hs s n b r c f : ℝ) ≤ C*(rowCount r c*s.recordWidth : ℕ)*
      ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hloadBound⟩ := CompactGadgetReservationHeadersCarvedBudget.uniform_bound c hc
  let K : ℝ := (CompactRowReservationBudget.constant c*c+1 : ℕ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs s n b r f hr hchunk hd hG hp hw hv hcan
  have hl := hloadBound hs s n b r f hr hchunk hd hG hp hw hv hcan
  have hp' : ((CompactRowReservationRun.budget c r s.recordWidth+1 : ℕ) : ℝ) ≤
      K*(rowCount r c*s.recordWidth : ℕ) := by
    dsimp only [K]
    exact_mod_cast reservation_bound s r c hr hc hp
  have he : 1 ≤ ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he
    (mul_nonneg hK (by positivity : 0 ≤ ((rowCount r c*s.recordWidth : ℕ) : ℝ)))
  unfold cost loadCost
  simp only [Nat.cast_add,Nat.cast_one] at hl hp' ⊢
  nlinarith only [hl,hp',hm]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedEndToEnd
