import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedRouting

/-! Original packing-width input is physically multiplied by n before exact
headers are synthesized inside the unchanged global compact reservation. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedCaller
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationData (rowCount)
open CompactGadgetReservationHeadersCaller (words originals headerWords permanent rowFocus rowFocus_injective actionFocus actionFocus_injective row_installed)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t : ℕ}

def widthFocus (B : Fin t) : Fin 3 → Fin (25+t) :=
  ![Fin.natAdd 25 B,Fin.castAdd t 3,Fin.castAdd t 10]
theorem widthFocus_injective (B : Fin t) : Function.Injective (widthFocus B) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp_all [widthFocus,Fin.ext_iff,Fin.val_natAdd,Fin.val_castAdd] <;> omega

def headerCost (hs : Fin 6 → List Bool) (r c w : ℕ) (f : Front) :=
  CompactGadgetReservationHeadersOps.bound (CompactGadgetReservationHeadersCarvedSchedule.schedule f)
    (CompactGadgetReservationHeadersCarvedSchedule.initial (headerWords hs r c) w)
def prepared (hs : Fin 6 → List Bool) (s : Shape) (n r c w : ℕ) (f : Front) (spectators : Tapes t prime) :=
  CompactGadgetReservationHeadersRouting.bank
    (CompactGadgetReservationHeadersCarvedSchedule.finished (headerWords hs r c) s n (rowCount r c) w f) spectators
def setupProgram (c : ℕ) (R B : Fin t) (f : Front) := seq (seq
  (CompactGadgetReservationHeadersRows.program (a := prime) c (rowFocus R) (rowFocus_injective R))
  (CompactGadgetReservationHeadersCore.productProgram (widthFocus B) (widthFocus_injective B)))
  (CompactGadgetReservationHeadersCarvedRouting.program (a := prime) f t)
def program (c : ℕ) (R B V X : Fin t) (hVX : V ≠ X) (f : Front) := seq
  (extend (setupProgram c R B f) CompactGadgetReservationPlacement.NativeTapes)
  (BinaryPackedOffsetOriginalPlaced.program (actionFocus V X) (actionFocus_injective V X hVX))

theorem width_installed (hs : Fin 7 → List Bool) (w : ℕ) (spectators : Tapes t prime) :
    setTape ((CompactGadgetReservationHeadersWords.common (a := prime)
      (CompactGadgetReservationHeadersSchedule.initial hs)).append spectators) (Fin.castAdd t 10)
      (RadixZeroFill.encodedBinary (bits w)) 1 =
      (CompactGadgetReservationHeadersWords.common
        (CompactGadgetReservationHeadersCarvedSchedule.initial hs w)).append spectators := by
  rw [SharedPlacementAlphabet.setTape_append_left,← CompactGadgetReservationHeadersWords.installs]
  rfl

theorem setup_runs (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (R B : Fin t)
    (rs bs : List Bool) (r c n b : ℕ) (s : Shape) (f : Front)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hr : 0 < r) (hc : 0 < c)
    (htR : spectators.tape R = RadixZeroFill.encodedBinary rs) (hhR : spectators.head R = 1)
    (hvB : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) (hb : 0 < b)
    (htB : spectators.tape B = RadixZeroFill.encodedBinary bs) (hhB : spectators.head B = 1)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : n*b ≤ s.H) :
    HoareTime (setupProgram c R B f)
      (fun v => v = CompactGadgetReservationHeadersCore.bank (permanent hs spectators))
      (fun v => v = prepared hs s n r c (n*b) f spectators)
      (CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+headerCost hs r c (n*b) f) := by
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
  let common := (CompactGadgetReservationHeadersWords.common (a := prime)
    (CompactGadgetReservationHeadersSchedule.initial (headerWords hs r c))).append spectators
  have hnval : Counter.value (hs 3) = n := by simpa [originals] using hv 3
  have hprod := CompactGadgetReservationHeadersCore.product common (widthFocus B) (widthFocus_injective B)
    bs (hs 3) n b hb hvB hnval cb (hcan 3)
    (by simpa only [common,widthFocus,Matrix.cons_val_zero,Tapes.append,Fin.addCases_right] using htB)
    (by simpa only [common,widthFocus,Matrix.cons_val_zero,Tapes.append,Fin.addCases_right] using hhB)
    (by simp [common,widthFocus,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.tape,CompactGadgetReservationHeadersSchedule.initial,
      headerWords,Tapes.append,Fin.addCases])
    (by simp [common,widthFocus,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases])
    (by simp [common,widthFocus,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.tape,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases])
    (by simp [common,widthFocus,CompactGadgetReservationHeadersWords.common,
      CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersSchedule.initial,
      Tapes.append,Fin.addCases])
  change HoareTime _ (fun v => v = CompactGadgetReservationHeadersCore.bank common)
    (fun v => v = CompactGadgetReservationHeadersCore.bank (setTape common (Fin.castAdd t 10)
      (RadixZeroFill.encodedBinary (bits (n*b))) 1)) _ at hprod
  dsimp only [common] at hprod
  rw [width_installed] at hprod
  have hvals : ∀ i, Counter.value (headerWords hs r c i) =
      CompactGadgetReservationHeadersCarvedSchedule.originalValues s n (rowCount r c) i := by
    intro i; fin_cases i <;> simp [headerWords,CompactGadgetReservationHeadersCarvedSchedule.originalValues,
      hv,originals,RecursiveChildQuotientsConstant.bits_value]
  have hcans : ∀ i, GrowingCounterData.Canonical (headerWords hs r c i) := by
    intro i; fin_cases i <;> simp [headerWords,hcan,RecursiveChildQuotientsConstant.bits_canonical]
  exact (hrow.seq hprod).seq (CompactGadgetReservationHeadersCarvedRouting.constructs (headerWords hs r c)
    s n (rowCount r c) (n*b) f spectators hvals hcans hK hd hG hw)

theorem spectator_tape (hs : Fin 6 → List Bool) (s : Shape) (n r c w : ℕ) (f : Front)
    (spectators : Tapes t prime) (i : Fin t) :
    (prepared hs s n r c w f spectators).tape (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.tape i := by
  simp only [prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem spectator_head (hs : Fin 6 → List Bool) (s : Shape) (n r c w : ℕ) (f : Front)
    (spectators : Tapes t prime) (i : Fin t) :
    (prepared hs s n r c w f spectators).head (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.head i := by
  simp only [prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem shape_sources (hs : Fin 6 → List Bool) (s : Shape) (n r c w : ℕ) (f : Front)
    (spectators : Tapes t prime) (V X : Fin t) :
    BinaryAdjacentWidthHeadersShared.Sources
      (SharedBank.payload (prepared hs s n r c w f spectators) (actionFocus V X))
      BinaryPackedOffsetOriginalRun.headers
      (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) w f) := by
  constructor
  · intro i
    fin_cases i
    all_goals simp only [SharedBank.payload,BinaryPackedOffsetOriginalRun.headers,actionFocus,

      prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,]
    all_goals simp [CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.tape,
      CompactGadgetReservationHeadersCarvedSchedule.finished,CompactGadgetReservationHeadersCarvedRouting.headerWords,
      BinaryRadixRangePrepare.values]
  · intro i
    fin_cases i
    all_goals simp only [SharedBank.payload,BinaryPackedOffsetOriginalRun.headers,actionFocus,

      prepared,CompactGadgetReservationHeadersRouting.bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,]
    all_goals simp [CompactGadgetReservationHeadersWords.common,CompactGadgetReservationHeadersWords.head,
      CompactGadgetReservationHeadersCarvedSchedule.finished]

theorem spectators_preserved (hs : Fin 6 → List Bool) (s : Shape) (n r c w : ℕ) (f : Front)
    (spectators : Tapes t prime) (V X i : Fin t) (hi : i ≠ X)
    (y : Fin (RadixRangePadding.volume (s.prefixRange (rowCount r c) f) (2^w) (gap s w f) (suffix s w)) → Bool) :
    (BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c w f spectators) (actionFocus V X) y).tape
      (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.tape i ∧
    (BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c w f spectators) (actionFocus V X) y).head
      (Fin.castAdd 15 (Fin.natAdd 25 i)) = spectators.head i := by
  have hne : Fin.castAdd 15 (Fin.natAdd 25 i) ≠ actionFocus V X 5 := by
    change Fin.castAdd 15 (Fin.natAdd 25 i) ≠ Fin.castAdd 15 (Fin.natAdd 25 X)
    intro h
    exact hi (Fin.natAdd_injective _ _ (Fin.castAdd_injective _ _ h))
  simp only [BinaryPackedOffsetOriginalPlaced.store,setTape,Function.update_of_ne hne,
    spectator_tape,spectator_head,and_self]

theorem runs (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (R B V X : Fin t) (hVX : V ≠ X)
    (rs bs : List Bool) (r c n b : ℕ) (s : Shape) (f : Front)
    (hvR : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hr : 0 < r) (hc : 0 < c)
    (htR : spectators.tape R = RadixZeroFill.encodedBinary rs) (hhR : spectators.head R = 1)
    (hvB : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) (hb : 0 < b)
    (htB : spectators.tape B = RadixZeroFill.encodedBinary bs) (hhB : spectators.head B = 1)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : n*b ≤ s.H)
    (hp : 0 < s.payload) (offsets : List Bool)
    (hV : offsets.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (n*b) (gap s (n*b) f)*(n*b))
    (htV : spectators.tape V = putWord (fun _ => blank) 0 (offsets.map bitSymbol))
    (hhV : spectators.head V = 0)
    (x : Fin (RadixRangePadding.volume (s.prefixRange (rowCount r c) f)
      (2^(n*b)) (gap s (n*b) f) (suffix s (n*b))) → Bool)
    (htX : spectators.tape X = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hhX : spectators.head X = 0) :
    HoareTime (program c R B V X hVX f)
      (fun v => v = (CompactGadgetReservationHeadersCore.bank (permanent hs spectators)).append
        (SharedBank.empty CompactGadgetReservationPlacement.NativeTapes prime))
      (fun v => v = CleanSubbank.bank (s := CompactGadgetReservationPlacement.NativeTapes)
        (BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c (n*b) f spectators) (actionFocus V X)
          (BinaryPackedOffsetData.result offsets (s.prefixRange (rowCount r c) f) (n*b)
            (gap s (n*b) f) (suffix s (n*b)) x)))
      (CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+headerCost hs r c (n*b) f+1+
        BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
          (n*b) (gap s (n*b) f) (suffix s (n*b))
          (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f)) := by
  have hsetup := hoare_extend_eq (setup_runs hs spectators R B rs bs r c n b s f hvR cr hr hc htR hhR
    hvB cb hb htB hhB hv hcan hK hd hG hw) (SharedBank.empty CompactGadgetReservationPlacement.NativeTapes prime)
  have hload := BinaryPackedOffsetOriginalPlaced.runs (prepared hs s n r c (n*b) f spectators)
    (actionFocus V X) (actionFocus_injective V X hVX) offsets
    (s.prefixRange (rowCount r c) f) (n*b) (gap s (n*b) f) (suffix s (n*b)) hV
    (s.prefix_pos _ f (CompactGadgetReservationData.rowCount_pos hc hr)) (gap_pos s (n*b) f)
    (suffix_pos s (n*b) hp) (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f)
    (CompactGadgetReservationHeadersCarvedRouting.header_values s (rowCount r c) (n*b) f)
    (CompactGadgetReservationHeadersCarvedRouting.header_canonical s (rowCount r c) (n*b) f)
    (shape_sources hs s n r c (n*b) f spectators V X)
    (by simpa [actionFocus,spectator_tape] using htV)
    (by simpa [actionFocus,spectator_head] using hhV) x
  have hstore : BinaryPackedOffsetOriginalPlaced.store (prepared hs s n r c (n*b) f spectators)
      (actionFocus V X) x = prepared hs s n r c (n*b) f spectators := by
    have ht : (prepared hs s n r c (n*b) f spectators).tape (actionFocus V X 5) =
        BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
      simpa [actionFocus,spectator_tape] using htX
    have hh : (prepared hs s n r c (n*b) f spectators).head (actionFocus V X 5) = 0 := by
      simpa [actionFocus,spectator_head] using hhX
    rw [BinaryPackedOffsetOriginalPlaced.store,← ht,← hh,SharedPlacementAlphabet.setTape_self]
  rw [hstore] at hload
  exact hsetup.seq hload

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedCaller
