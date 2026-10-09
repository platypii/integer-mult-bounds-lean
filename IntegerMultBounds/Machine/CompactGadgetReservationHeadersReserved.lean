import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCaller

/-! Complete synthesized-shape load on the actual reservation endpoint.
Only original global layout headers and a physical offset word are inputs. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersReserved
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount roleSlot)
open CompactGadgetReservationPlacement (ReservationTapes NativeTapes)
variable {c r : ℕ}

def rowSlot (c : ℕ) : Fin (ReservationTapes c) :=
  Fin.castAdd (CompactRowReservationPlacement.NativeTapes c) (Fin.castAdd c (2 : Fin 25))
def Rslot (c : ℕ) : Fin (ReservationTapes c+1) := Fin.castAdd 1 (rowSlot c)
def Vslot (c : ℕ) : Fin (ReservationTapes c+1) := Fin.natAdd (ReservationTapes c) 0
def Xslot (c : ℕ) (j : Fin c) : Fin (ReservationTapes c+1) := Fin.castAdd 1 (roleSlot c j)
theorem offset_role_distinct (c : ℕ) (j : Fin c) : Vslot c ≠ Xslot c j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Vslot,Xslot,Fin.val_natAdd,Fin.val_castAdd] at hv
  have hl := (roleSlot c j).isLt
  omega

def offsets (V : List Bool) : Tapes 1 prime :=
  ⟨fun _ => 0,fun _ => putWord (fun _ => blank) 0 (V.map bitSymbol)⟩
def spectators (hc : 0 < c) (s : Shape) (x : Fin (1*r*s.recordWidth) → Bool)
    (rs ls : List Bool) (V : List Bool) :=
  (CompactRowReservationEndpoint.final (a := prime) hc x rs ls).append (offsets V)
def program (c : ℕ) (j : Fin c) (f : Front) :=
  CompactGadgetReservationHeadersCaller.program c (Rslot c) (Vslot c) (Xslot c j)
    (offset_role_distinct c j) f

theorem runs (hc : 0 < c) (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool) (j : Fin c) (V : List Bool)
    (hs : Fin 6 → List Bool)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) (hr : 0 < r)
    (hv : ∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersCaller.originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hp : 0 < s.payload)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n) :
    HoareTime (program c j f)
      (fun v => v = (CompactGadgetReservationHeadersCore.bank
        (CompactGadgetReservationHeadersCaller.permanent hs (spectators hc s x rs ls V))).append
          (SharedBank.empty NativeTapes prime))
      (fun v => v = CleanSubbank.bank (s := NativeTapes)
        (BinaryPackedOffsetOriginalPlaced.store
          (CompactGadgetReservationHeadersCaller.prepared hs s n r c f (spectators hc s x rs ls V))
          (CompactGadgetReservationHeadersCaller.actionFocus (Vslot c) (Xslot c j))
          (CompactGadgetReservationRun.output s n hn f hc x j V)))
      (CompactGadgetReservationHeadersRows.cost r c+1+
        CompactGadgetReservationHeadersCaller.headerCost hs r c f+1+
        BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
          (s.width n) (s.gap n f) (s.suffix n)
          (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f)) := by
  have htR : (spectators hc s x rs ls V).tape (Rslot c) = RadixZeroFill.encodedBinary rs := by
    simpa only [spectators,Rslot,rowSlot,Tapes.append,Fin.addCases_left] using
      (CompactRowReservationEndpoint.original_headers (a := prime) hc x rs ls).2.1
  have hhR : (spectators hc s x rs ls V).head (Rslot c) = 1 := by
    simpa only [spectators,Rslot,rowSlot,Tapes.append,Fin.addCases_left] using
      (CompactRowReservationEndpoint.original_headers (a := prime) hc x rs ls).1
  have htV : (spectators hc s x rs ls V).tape (Vslot c) = putWord (fun _ => blank) 0 (V.map bitSymbol) := by
    simp only [spectators,Vslot,Tapes.append,Fin.addCases_right,offsets]
  have hhV : (spectators hc s x rs ls V).head (Vslot c) = 0 := by
    simp only [spectators,Vslot,Tapes.append,Fin.addCases_right,offsets]
  have htX : (spectators hc s x rs ls V).tape (Xslot c j) =
      BinaryRadixRangePrepareAlphabet.word
        (fun i => bitSymbol (CompactGadgetReservationData.rectangle (a := prime) s n hn f hc x j i)) := by
    simpa only [spectators,Xslot,Tapes.append,Fin.addCases_left,
      BinaryRadixRangePrepareAlphabet.word] using
      (CompactGadgetReservationData.role_tape (a := prime) s n hn f hc x rs ls j).2
  have hhX : (spectators hc s x rs ls V).head (Xslot c j) = 0 := by
    simpa only [spectators,Xslot,Tapes.append,Fin.addCases_left] using
      (CompactGadgetReservationData.role_tape (a := prime) s n hn f hc x rs ls j).1
  exact CompactGadgetReservationHeadersCaller.runs hs (spectators hc s x rs ls V)
    (Rslot c) (Vslot c) (Xslot c j) (offset_role_distinct c j) rs r c n s f
    hvR cr hr hc htR hhR hv hcan hK hd hG hn hp V hV htV hhV
    (CompactGadgetReservationData.rectangle (a := prime) s n hn f hc x j) htX hhX

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersReserved
