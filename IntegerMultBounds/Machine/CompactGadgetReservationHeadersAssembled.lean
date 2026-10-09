import IntegerMultBounds.Machine.CompactGadgetReservationHeadersEndpoint
import IntegerMultBounds.Machine.CompactGadgetReservationEndpoint

/-! Paid original-row reservation followed by the actual reserved load.
The load theorem is instantiated internally from physical source tapes. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersAssembled
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount)
open CompactGadgetReservationEndpoint
variable {c r : ℕ}

theorem original_tape (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) (j : Fin c) (i : Fin 5) :
    (localCaller hc s x rs ls originals j).tape (Fin.castAdd 1 i) = originals.tape i := by
  simp only [localCaller,common,SharedBank.payload,CompactGadgetReservationPlacement.commonSlots,
    Fin.addCases_left,Tapes.append,Fin.addCases_right]

theorem original_head (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) (j : Fin c) (i : Fin 5) :
    (localCaller hc s x rs ls originals j).head (Fin.castAdd 1 i) = originals.head i := by
  simp only [localCaller,common,SharedBank.payload,CompactGadgetReservationPlacement.commonSlots,
    Fin.addCases_left,Tapes.append,Fin.addCases_right]

theorem reserve_then_load (ha : 2 ≤ prime) (hc : 0 < c) (s : Shape) (n : ℕ)
    (hn : n ≤ s.axes) (f : Front) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (originals : Tapes 5 prime) (j : Fin c) (V : List Bool)
    (hvR : Counter.value rs = r) (hvL : Counter.value ls = s.recordWidth)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hr : 0 < r) (hp : 0 < s.payload)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n)
    (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values
      (s.prefixRange (rowCount r c) f) (s.gap n f) (s.suffix n) (s.width n) i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsrc : BinaryAdjacentWidthHeadersShared.Sources originals (Fin.castAdd 1) hs)
    (htV : originals.tape 4 =
      putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank)) 0 (V.map bitSymbol))
    (hhV : originals.head 4 = 0) :
    HoareTime (reserveAndLoad ha c j)
      (fun v => v = source (c := c) s x rs ls originals)
      (fun v => v = after hc s n hn f x rs ls originals j V)
      ((CompactRowReservationBudget.constant c*(c+1))*(r*s.recordWidth)+1+
        BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
          (s.width n) (s.gap n f) (s.suffix n) hs) := by
  have he (i : Fin 4) : BinaryPackedOffsetOriginalRun.headers i = Fin.castAdd 1 (Fin.castAdd 1 i) := by
    fin_cases i <;> rfl
  have hsrc' : BinaryAdjacentWidthHeadersShared.Sources (localCaller hc s x rs ls originals j)
      BinaryPackedOffsetOriginalRun.headers hs := by
    constructor
    · intro i
      rw [he,original_tape]
      exact hsrc.tape i
    · intro i
      rw [he,original_head]
      exact hsrc.head i
  have htV' : (localCaller hc s x rs ls originals j).tape 4 =
      putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank)) 0 (V.map bitSymbol) := by
    change (localCaller hc s x rs ls originals j).tape (Fin.castAdd 1 (4 : Fin 5)) = _
    rw [original_tape]
    exact htV
  have hhV' : (localCaller hc s x rs ls originals j).head 4 = 0 := by
    change (localCaller hc s x rs ls originals j).head (Fin.castAdd 1 (4 : Fin 5)) = _
    rw [original_head]
    exact hhV
  exact CompactGadgetReservationEndpoint.reserve_then_load ha hc s n hn f x rs ls originals j V _
    hvR hvL cr cl hr hp (runs hc s n hn f x rs ls originals j hr hp V hV hs hv hcan hsrc' htV' hhV')

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersAssembled
