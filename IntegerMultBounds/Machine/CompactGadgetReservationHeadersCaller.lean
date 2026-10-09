import IntegerMultBounds.Machine.CompactGadgetReservationHeadersRouting
import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalPlaced

/-! The original row descriptor and six original layout descriptors physically
produce every shape input consumed by the real packed action. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCaller
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t : ℕ}

def words (hs : Fin 6 → List Bool) : CompactGadgetReservationHeadersWords.Words := fun i =>
  if h : i.val < 5 then some (hs ⟨i.val,by omega⟩) else if i = 6 then some (hs 5) else none
def originals (s : Shape) (n : ℕ) : Fin 6 → ℕ := ![s.chunk,s.axes,s.guard,n,s.active,s.payload]
def headerWords (hs : Fin 6 → List Bool) (r c : ℕ) : Fin 7 → List Bool :=
  ![hs 0,hs 1,hs 2,hs 3,hs 4,bits (rowCount r c),hs 5]
def permanent (hs : Fin 6 → List Bool) (spectators : Tapes t prime) :=
  (CompactGadgetReservationHeadersWords.common (a := prime) (words hs)).append spectators
def rowFocus (R : Fin t) : Fin 4 → Fin (25+t) :=
  ![Fin.natAdd 25 R,Fin.castAdd t 7,Fin.castAdd t 8,Fin.castAdd t 5]
theorem rowFocus_injective (R : Fin t) : Function.Injective (rowFocus R) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp_all [rowFocus,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega

def actionFocus (V X : Fin t) : Fin 6 → Fin ((25+t)+15) :=
  ![Fin.castAdd 15 (Fin.castAdd t 21),Fin.castAdd 15 (Fin.castAdd t 23),
    Fin.castAdd 15 (Fin.castAdd t 24),Fin.castAdd 15 (Fin.castAdd t 10),
    Fin.castAdd 15 (Fin.natAdd 25 V),Fin.castAdd 15 (Fin.natAdd 25 X)]
theorem actionFocus_injective (V X : Fin t) (hVX : V ≠ X) : Function.Injective (actionFocus V X) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hvx : V.val ≠ X.val := fun he => hVX (Fin.ext he)
  fin_cases i <;> fin_cases j <;> simp_all [actionFocus,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega

def headerCost (hs : Fin 6 → List Bool) (r c : ℕ) (f : Front) :=
  CompactGadgetReservationHeadersOps.bound (CompactGadgetReservationHeadersSchedule.schedule f)
    (CompactGadgetReservationHeadersSchedule.initial (headerWords hs r c))
def prepared (hs : Fin 6 → List Bool) (s : Shape) (n r c : ℕ) (f : Front) (spectators : Tapes t prime) :=
  CompactGadgetReservationHeadersRouting.bank
    (CompactGadgetReservationHeadersSchedule.finished (headerWords hs r c) s n (rowCount r c) f) spectators

def setupProgram (c : ℕ) (R : Fin t) (f : Front) := seq
  (CompactGadgetReservationHeadersRows.program (a := prime) c (rowFocus R) (rowFocus_injective R))
  (CompactGadgetReservationHeadersRouting.program (a := prime) f t)
def program (c : ℕ) (R V X : Fin t) (hVX : V ≠ X) (f : Front) := seq
  (extend (setupProgram c R f) CompactGadgetReservationPlacement.NativeTapes)
  (BinaryPackedOffsetOriginalPlaced.program (actionFocus V X) (actionFocus_injective V X hVX))

theorem row_installed (hs : Fin 6 → List Bool) (r c : ℕ) (spectators : Tapes t prime) :
    setTape (permanent hs spectators) (Fin.castAdd t 5)
      (RadixZeroFill.encodedBinary (bits (rowCount r c))) 1 =
    (CompactGadgetReservationHeadersWords.common
      (CompactGadgetReservationHeadersSchedule.initial (headerWords hs r c))).append spectators := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => fin_cases i <;> simp [permanent,words,headerWords,
      CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.head,
      CompactGadgetReservationHeadersWords.tape,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases]
  | right i =>
      have hi : Fin.natAdd 25 i ≠ (Fin.castAdd t (5 : Fin 25)) := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp only [permanent,Function.update_of_ne hi,Tapes.append,Fin.addCases_right]

theorem setup_runs (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (R : Fin t)
    (rs : List Bool) (r c n : ℕ) (s : Shape) (f : Front)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hr : 0 < r) (hc : 0 < c)
    (htR : spectators.tape R = RadixZeroFill.encodedBinary rs) (hhR : spectators.head R = 1)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hn : n ≤ s.axes) :
    HoareTime (setupProgram c R f)
      (fun v => v = CompactGadgetReservationHeadersCore.bank (permanent hs spectators))
      (fun v => v = prepared hs s n r c f spectators)
      (CompactGadgetReservationHeadersRows.cost r c+1+headerCost hs r c f) := by
  have hrow := CompactGadgetReservationHeadersRows.constructs (permanent hs spectators) c
    (rowFocus R) (rowFocus_injective R) rs r hvR cr hr hc
    (by simpa only [permanent,rowFocus,Matrix.cons_val_zero,Tapes.append,Fin.addCases_right] using htR)
    (by simpa only [permanent,rowFocus,Matrix.cons_val_zero,Tapes.append,Fin.addCases_right] using hhR)
    (by intro i hi; fin_cases i <;> simp_all [permanent,rowFocus,words,
      CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.head,
      CompactGadgetReservationHeadersWords.tape,Tapes.append,Fin.addCases])
  change HoareTime _ _ (fun v => v = CompactGadgetReservationHeadersCore.bank
    (setTape (permanent hs spectators) (Fin.castAdd t 5)
      (RadixZeroFill.encodedBinary (bits (rowCount r c))) 1)) _ at hrow
  rw [row_installed] at hrow
  have hvals : ∀ i, Counter.value (headerWords hs r c i) =
      CompactGadgetReservationHeadersSchedule.originalValues s n (rowCount r c) i := by
    intro i; fin_cases i <;> simp [headerWords,CompactGadgetReservationHeadersSchedule.originalValues,
      hv,originals,RecursiveChildQuotientsConstant.bits_value]
  have hcans : ∀ i, GrowingCounterData.Canonical (headerWords hs r c i) := by
    intro i; fin_cases i <;> simp [headerWords,hcan,RecursiveChildQuotientsConstant.bits_canonical]
  exact hrow.seq (CompactGadgetReservationHeadersRouting.constructs (headerWords hs r c) s n
    (rowCount r c) f spectators hvals hcans hK hd hG hn)

theorem spectator_tape (hs : Fin 6 → List Bool) (s : Shape) (n r c : ℕ) (f : Front)
    (spectators : Tapes t prime) (i : Fin t) :
    (prepared hs s n r c f spectators).tape (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.tape i := by
  simp only [prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem spectator_head (hs : Fin 6 → List Bool) (s : Shape) (n r c : ℕ) (f : Front)
    (spectators : Tapes t prime) (i : Fin t) :
    (prepared hs s n r c f spectators).head (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.head i := by
  simp only [prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem shape_sources (hs : Fin 6 → List Bool) (s : Shape) (n r c : ℕ) (f : Front)
    (spectators : Tapes t prime) (V X : Fin t) :
    BinaryAdjacentWidthHeadersShared.Sources
      (SharedBank.payload (prepared hs s n r c f spectators) (actionFocus V X))
      BinaryPackedOffsetOriginalRun.headers
      (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f) := by
  constructor
  · intro i
    fin_cases i
    all_goals simp only [SharedBank.payload,BinaryPackedOffsetOriginalRun.headers,actionFocus,

      prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,]
    all_goals simp [CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.tape,
      CompactGadgetReservationHeadersSchedule.finished,CompactGadgetReservationHeadersEndpoint.headerWords,
      BinaryRadixRangePrepare.values]
  · intro i
    fin_cases i
    all_goals simp only [SharedBank.payload,BinaryPackedOffsetOriginalRun.headers,actionFocus,

      prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,]
    all_goals simp [CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.head,
      CompactGadgetReservationHeadersSchedule.finished]

theorem runs (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (R V X : Fin t) (hVX : V ≠ X)
    (rs : List Bool) (r c n : ℕ) (s : Shape) (f : Front)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hr : 0 < r) (hc : 0 < c)
    (htR : spectators.tape R = RadixZeroFill.encodedBinary rs) (hhR : spectators.head R = 1)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hn : n ≤ s.axes)
    (hp : 0 < s.payload) (offsets : List Bool)
    (hV : offsets.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n)
    (htV : spectators.tape V = putWord (fun _ => blank) 0 (offsets.map bitSymbol))
    (hhV : spectators.head V = 0)
    (x : Fin (RadixRangePadding.volume (s.prefixRange (rowCount r c) f)
      (2^(s.width n)) (s.gap n f) (s.suffix n)) → Bool)
    (htX : spectators.tape X = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hhX : spectators.head X = 0) :
    HoareTime (program c R V X hVX f)
      (fun v => v = (CompactGadgetReservationHeadersCore.bank (permanent hs spectators)).append
        (SharedBank.empty CompactGadgetReservationPlacement.NativeTapes prime))
      (fun v => v = CleanSubbank.bank (s := CompactGadgetReservationPlacement.NativeTapes)
        (BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c f spectators) (actionFocus V X)
          (BinaryPackedOffsetData.result offsets (s.prefixRange (rowCount r c) f) (s.width n)
            (s.gap n f) (s.suffix n) x)))
      (CompactGadgetReservationHeadersRows.cost r c+1+headerCost hs r c f+1+
        BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
          (s.width n) (s.gap n f) (s.suffix n)
          (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f)) := by
  have hsetup := hoare_extend_eq (setup_runs hs spectators R rs r c n s f hvR cr hr hc htR hhR
    hv hcan hK hd hG hn) (SharedBank.empty CompactGadgetReservationPlacement.NativeTapes prime)
  have hload := BinaryPackedOffsetOriginalPlaced.runs (prepared hs s n r c f spectators)
    (actionFocus V X) (actionFocus_injective V X hVX) offsets
    (s.prefixRange (rowCount r c) f) (s.width n) (s.gap n f) (s.suffix n) hV
    (s.prefix_pos _ f (CompactGadgetReservationData.rowCount_pos hc hr)) (s.gap_pos n f)
    (s.suffix_pos n hp) (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f)
    (CompactGadgetReservationHeadersEndpoint.header_values s n (rowCount r c) f)
    (CompactGadgetReservationHeadersEndpoint.header_canonical s n (rowCount r c) f)
    (shape_sources hs s n r c f spectators V X)
    (by simpa [actionFocus,spectator_tape] using htV)
    (by simpa [actionFocus,spectator_head] using hhV) x
  have hstore : BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c f spectators)
      (actionFocus V X) x = prepared hs s n r c f spectators := by
    have ht : (prepared hs s n r c f spectators).tape (actionFocus V X 5) =
        BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
      simpa [actionFocus,spectator_tape] using htX
    have hh : (prepared hs s n r c f spectators).head (actionFocus V X 5) = 0 := by
      simpa [actionFocus,spectator_head] using hhX
    rw [BinaryPackedOffsetOriginalPlaced.store,← ht,← hh,SharedPlacementAlphabet.setTape_self]
  rw [hstore] at hload
  exact hsetup.seq hload

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCaller
