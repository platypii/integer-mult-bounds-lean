import IntegerMultBounds.Machine.ActiveRepairLateFieldsRun

/-! Physically erase the recovered pre-toggle target; retain only the actual
repair destination words and flag, originals, headers and full scan counter. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsCleanup
noncomputable section
open ActiveRepairLateFieldsBank
open CountedGuardGadgetRecord (word)

def program := WordBankCleanup.clearProgram (0 : Fin 35) (by decide) 1

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  WordBankCleanup.write (toggled q b hb hbq V W U X cs hs) 0 (fun _ => blank)

private theorem working_clean_eq (A B C X T V W U cs : List Bool)
    (hs : Fin 3 → List Bool) (fl : Bool) :
    WordBankCleanup.write ((CountedLateRepairToggle.working A B C X T hs fl).append
      (originals V W U cs)) 0 (fun _ => blank) =
      SharedPlacementAlphabet.setTape
        (SharedPlacementAlphabet.setTape
          (SharedPlacementAlphabet.setTape
            (SharedPlacementAlphabet.setTape (before V W U X cs hs) 1 (word B) 0) 2 (word C) 0) 28
            (CountedLateRepairFlag.key fl) 1) 30 (word T) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | (change RadixZeroFill.encodedBinary _=CountedLoopReuseAlphabet.binary _; exact (CountedGuardGadgetHeaders.binary_eq _).symm)

theorem output_eq (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    output q b hb hbq V W U X cs hs =
      SharedPlacementAlphabet.setTape
        (SharedPlacementAlphabet.setTape
          (SharedPlacementAlphabet.setTape
            (SharedPlacementAlphabet.setTape (before V W U X cs hs) 1
              (word (CountedLateRepairInverse.temp q b hb hbq V W U X)) 0) 2
              (word (CountedLateRepairInverse.restored b hb U X)) 0) 28
            (CountedLateRepairFlag.key (CountedLateRepairGuard.flag q b V W X ||
              CountedLateRepairGuard.flag q b V U X)) 1) 30
          (word (CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U X) X)) 0 := by
  exact working_clean_eq _ _ _ _ _ _ _ _ _ _ _

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    HoareTime program (fun z => z=toggled q b hb hbq V W U X cs hs)
      (fun z => z=output q b hb hbq V W U X cs hs) (5*((X.length+1)*(q+b+1))) := by
  have h := WordBankCleanup.clear_hoare (toggled q b hb hbq V W U X cs hs) 0 (by decide)
    ((CountedLateRepairInverse.target q b hb hbq V W U X).map bitSymbol)
    (ReturnOrigin.bits_nonblank _) (by
      simp only [toggled,CountedLateRepairToggle.after,CountedLateRepairToggle.working,
        CountedPackedLateRun.bank,CountedPackedLateRun.payload,Tapes.append]
      rfl)
  obtain ⟨_,_,_,_,ht,_⟩ := CountedLateRepairInverse.lengths q b hb hbq V W U X hV hW hU
  apply h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [List.length_map,ht,hV]
  nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsCleanup
