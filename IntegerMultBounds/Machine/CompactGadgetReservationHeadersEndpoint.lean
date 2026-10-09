import IntegerMultBounds.Machine.CompactGadgetReservationHeadersSchedule
import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalRun

/-! Exact physical original-header sources for the reserved compact load.
All seven original inputs survive; only four generated descriptors remain. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersEndpoint
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersSchedule
open CompactGadgetReservationHeadersWords (bank common)
variable {a : ℕ}

def headerWords (s : Shape) (n rows : ℕ) (f : Front) : Fin 4 → List Bool :=
  fun i => RecursiveChildQuotientsConstant.bits
    (BinaryRadixRangePrepare.values (s.prefixRange rows f) (s.gap n f) (s.suffix n) (s.width n) i)
def headerSlots (i : Fin 4) : Fin 40 := Fin.castAdd 15 (outputSlots i)

theorem headerSlots_injective : Function.Injective headerSlots := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headerSlots,outputSlots]

theorem header_values (s : Shape) (n rows : ℕ) (f : Front) :
    ∀ i, Counter.value (headerWords s n rows f i) =
      BinaryRadixRangePrepare.values (s.prefixRange rows f) (s.gap n f) (s.suffix n) (s.width n) i :=
  fun _i => RecursiveChildQuotientsConstant.bits_value _

theorem header_canonical (s : Shape) (n rows : ℕ) (f : Front) :
    ∀ i, GrowingCounterData.Canonical (headerWords s n rows f i) :=
  fun _i => RecursiveChildQuotientsConstant.bits_canonical _

/-- These are literal marked tape words at original-header ports, ready for
the already proved original-header field-swap/rotation/swap machine. -/
theorem sources (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front) :
    BinaryAdjacentWidthHeadersShared.Sources (bank (a := a) (finished hs s n rows f))
      headerSlots (headerWords s n rows f) := by
  constructor
  · intro i
    simp only [headerSlots,bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    fin_cases i <;> simp [common,finished,outputSlots,headerWords,
      BinaryRadixRangePrepare.values,CompactGadgetReservationHeadersWords.tape]
  · intro i
    simp only [headerSlots,bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    fin_cases i <;> simp [common,finished,outputSlots,CompactGadgetReservationHeadersWords.head]

theorem originals (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front) (i : Fin 7) :
    (bank (a := a) (finished hs s n rows f)).head (Fin.castAdd 15 (Fin.castAdd 18 i)) = 1 ∧
    (bank (a := a) (finished hs s n rows f)).tape (Fin.castAdd 15 (Fin.castAdd 18 i)) =
      RadixZeroFill.encodedBinary (hs i) := by
  simp only [bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
    Tapes.append,Fin.addCases_left,common,finished,Fin.val_castAdd,dite_eq_left i.isLt,
    CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersWords.tape,and_self]

theorem intermediate_blank (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front)
    (i : Fin 25) (hOrig : 7 ≤ i.val)
    (hP : i ≠ 21) (hG : i ≠ 23) (hB : i ≠ 24) (hw : i ≠ 10) :
    (bank (a := a) (finished hs s n rows f)).head (Fin.castAdd 15 i) = 0 ∧
    (bank (a := a) (finished hs s n rows f)).tape (Fin.castAdd 15 i) = fun _ => blank := by
  simp only [bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
    Tapes.append,Fin.addCases_left,common,finished,show ¬i.val < 7 by omega,
    ↓reduceDIte,hP,hG,hB,hw,↓reduceIte,
    CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersWords.tape,and_self]

theorem private_blank (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front) (i : Fin 15) :
    (bank (a := a) (finished hs s n rows f)).head (Fin.natAdd 25 i) = 0 ∧
    (bank (a := a) (finished hs s n rows f)).tape (Fin.natAdd 25 i) = fun _ => blank := by
  simp only [bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
    Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersEndpoint
