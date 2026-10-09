import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedCaller
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersReserved

/-! Complete synthesized-shape load on the actual reservation endpoint.
Only original global layout headers and a physical offset word are inputs. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReserved
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount roleSlot)
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationPlacement (ReservationTapes NativeTapes)
variable {c r : ℕ}

def Rslot (c : ℕ) : Fin ((ReservationTapes c+1)+1) :=
  Fin.castAdd 1 (CompactGadgetReservationHeadersReserved.Rslot c)
def Vslot (c : ℕ) : Fin ((ReservationTapes c+1)+1) :=
  Fin.castAdd 1 (CompactGadgetReservationHeadersReserved.Vslot c)
def Xslot (c : ℕ) (j : Fin c) : Fin ((ReservationTapes c+1)+1) :=
  Fin.castAdd 1 (CompactGadgetReservationHeadersReserved.Xslot c j)
def Bslot (c : ℕ) : Fin ((ReservationTapes c+1)+1) := Fin.natAdd (ReservationTapes c+1) 0
theorem offset_role_distinct (c : ℕ) (j : Fin c) : Vslot c ≠ Xslot c j := by
  intro h
  exact CompactGadgetReservationHeadersReserved.offset_role_distinct c j (Fin.castAdd_injective _ _ h)
def packing (bs : List Bool) : Tapes 1 prime :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary bs⟩
def spectators (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls bs : List Bool) (V : List Bool) :=
  (CompactGadgetReservationHeadersReserved.spectators hc s x rs ls V).append (packing bs)
def program (c : ℕ) (j : Fin c) (f : Front) :=
  CompactGadgetReservationHeadersCarvedCaller.program c (Rslot c) (Bslot c) (Vslot c) (Xslot c j)
    (offset_role_distinct c j) f
def output (hc : 0 < c) (s : Shape) (n b : ℕ) (hw : n*b ≤ s.H) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (j : Fin c) (V : List Bool) :=
  BinaryPackedOffsetData.result V (s.prefixRange (rowCount r c) f) (n*b) (gap s (n*b) f) (suffix s (n*b))
    (rectangle (a := prime) s (n*b) hw f hc x j)

theorem runs (hc : 0 < c) (s : Shape) (n b : ℕ) (hn : n ≤ s.axes) (hb : b ≤ s.guard) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls bs : List Bool) (j : Fin c) (V : List Bool)
    (hs : Fin 6 → List Bool)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) (hr : 0 < r)
    (hvB : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) (hbpos : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersCaller.originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hp : 0 < s.payload)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (n*b) (gap s (n*b) f)*(n*b)) :
    HoareTime (program c j f)
      (fun v => v = (CompactGadgetReservationHeadersCore.bank
        (CompactGadgetReservationHeadersCaller.permanent hs (spectators hc s x rs ls bs V))).append
          (SharedBank.empty NativeTapes prime))
      (fun v => v = CleanSubbank.bank (s := NativeTapes)
        (BinaryPackedOffsetOriginalPlaced.store
          (CompactGadgetReservationHeadersCarvedCaller.prepared hs s n r c (n*b) f (spectators hc s x rs ls bs V))
          (CompactGadgetReservationHeadersCaller.actionFocus (Vslot c) (Xslot c j))
          (output hc s n b (packed_width_le s n b hn hb) f x j V)))
      (CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+
        CompactGadgetReservationHeadersCarvedCaller.headerCost hs r c (n*b) f+1+
        BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
          (n*b) (gap s (n*b) f) (suffix s (n*b))
          (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f)) := by
  have htR : (spectators hc s x rs ls bs V).tape (Rslot c) = RadixZeroFill.encodedBinary rs := by
    simpa only [spectators,Rslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Rslot,CompactGadgetReservationHeadersReserved.rowSlot,Tapes.append,Fin.addCases_left] using
      (CompactRowReservationEndpoint.original_headers (a := prime) hc x rs ls).2.1
  have hhR : (spectators hc s x rs ls bs V).head (Rslot c) = 1 := by
    simpa only [spectators,Rslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Rslot,CompactGadgetReservationHeadersReserved.rowSlot,Tapes.append,Fin.addCases_left] using
      (CompactRowReservationEndpoint.original_headers (a := prime) hc x rs ls).1
  have htV : (spectators hc s x rs ls bs V).tape (Vslot c) = putWord (fun _ => blank) 0 (V.map bitSymbol) := by
    simp only [spectators,Vslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Vslot,Tapes.append,Fin.addCases_left,Fin.addCases_right,CompactGadgetReservationHeadersReserved.offsets]
  have hhV : (spectators hc s x rs ls bs V).head (Vslot c) = 0 := by
    simp only [spectators,Vslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Vslot,Tapes.append,Fin.addCases_left,Fin.addCases_right,CompactGadgetReservationHeadersReserved.offsets]
  have htX : (spectators hc s x rs ls bs V).tape (Xslot c j) =
      BinaryRadixRangePrepareAlphabet.word
        (fun i => bitSymbol (rectangle (a := prime) s (n*b) (packed_width_le s n b hn hb) f hc x j i)) := by
    simpa only [spectators,Xslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Xslot,Tapes.append,Fin.addCases_left,
      BinaryRadixRangePrepareAlphabet.word] using
      (role_tape (a := prime) s (n*b) (packed_width_le s n b hn hb) f hc x rs ls j).2
  have hhX : (spectators hc s x rs ls bs V).head (Xslot c j) = 0 := by
    simpa only [spectators,Xslot,CompactGadgetReservationHeadersReserved.spectators,CompactGadgetReservationHeadersReserved.Xslot,Tapes.append,Fin.addCases_left] using
      (role_tape (a := prime) s (n*b) (packed_width_le s n b hn hb) f hc x rs ls j).1
  have htB : (spectators hc s x rs ls bs V).tape (Bslot c) = RadixZeroFill.encodedBinary bs := by
    simp only [spectators,Bslot,Tapes.append,Fin.addCases_right,packing]
  have hhB : (spectators hc s x rs ls bs V).head (Bslot c) = 1 := by
    simp only [spectators,Bslot,Tapes.append,Fin.addCases_right,packing]
  exact CompactGadgetReservationHeadersCarvedCaller.runs hs (spectators hc s x rs ls bs V)
    (Rslot c) (Bslot c) (Vslot c) (Xslot c j) (offset_role_distinct c j) rs bs r c n b s f
    hvR cr hr hc htR hhR hvB cb hbpos htB hhB hv hcan hK hd hG
    (packed_width_le s n b hn hb) hp V hV htV hhV
    (rectangle (a := prime) s (n*b) (packed_width_le s n b hn hb) f hc x j) htX hhX

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReserved
