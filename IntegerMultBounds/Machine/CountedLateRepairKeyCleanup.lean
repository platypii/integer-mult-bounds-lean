import IntegerMultBounds.Machine.CountedLateRepairKeyWrite

/-! Physically erase every generated later-key word and the consumed flag.
The original controls, descriptors, scan counter and marked key are retained. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyCleanup
noncomputable section
open CountedLateRepairKeyBank
open CountedGuardGadgetRecord (word)

def clear (i : Fin 34) := WordBankCleanup.clearProgram i (by decide) 1

theorem clearV (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    HoareTime (clear 0) (fun v => v=bank V W U X T D hs cs F K pf pk)
      (fun v => v=bank [] W U X T D hs cs F K pf pk) (2*V.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs F K pf pk)
    (0 : Fin 34) (by decide) (V.map bitSymbol) (ReturnOrigin.bits_nonblank V) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem clearW (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    HoareTime (clear 1) (fun v => v=bank V W U X T D hs cs F K pf pk)
      (fun v => v=bank V [] U X T D hs cs F K pf pk) (2*W.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs F K pf pk)
    (1 : Fin 34) (by decide) (W.map bitSymbol) (ReturnOrigin.bits_nonblank W) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem clearU (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    HoareTime (clear 2) (fun v => v=bank V W U X T D hs cs F K pf pk)
      (fun v => v=bank V W [] X T D hs cs F K pf pk) (2*U.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs F K pf pk)
    (2 : Fin 34) (by decide) (U.map bitSymbol) (ReturnOrigin.bits_nonblank U) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem clearT (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    HoareTime (clear 32) (fun v => v=bank V W U X T D hs cs F K pf pk)
      (fun v => v=bank V W U X [] D hs cs F K pf pk) (2*T.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs F K pf pk)
    (32 : Fin 34) (by decide) (T.map bitSymbol) (ReturnOrigin.bits_nonblank T) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem clearD (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    HoareTime (clear 33) (fun v => v=bank V W U X T D hs cs F K pf pk)
      (fun v => v=bank V W U X T [] hs cs F K pf pk) (2*D.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs F K pf pk)
    (33 : Fin 34) (by decide) (D.map bitSymbol) (ReturnOrigin.bits_nonblank D) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

theorem clearF (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool) (fl : Bool)
    (K : ℤ → Fin 5) (pk : ℤ) :
    HoareTime (clear 28) (fun v => v=bank V W U X T D hs cs (CountedLateRepairFlag.key fl) K 0 pk)
      (fun v => v=bank V W U X T D hs cs (fun _ => blank) K 0 pk) 5 := by
  have h := WordBankCleanup.clear_hoare (bank V W U X T D hs cs (CountedLateRepairFlag.key fl) K 0 pk)
    (28 : Fin 34) (by decide) ([fl].map bitSymbol) (ReturnOrigin.bits_nonblank [fl]) rfl
  refine h.consequence (fun _ h => h) ?_ (by simp)
  rintro v rfl
  unfold WordBankCleanup.write
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> rfl

def program := seq (seq (seq (seq (seq (clear 0) (clear 1)) (clear 2)) (clear 32)) (clear 33)) (clear 28)

theorem runs_words (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool) (fl : Bool)
    (K : ℤ → Fin 5) (pk : ℤ) :
    HoareTime program (fun v => v=bank V W U X T D hs cs (CountedLateRepairFlag.key fl) K 0 pk)
      (fun v => v=bank [] [] [] X [] [] hs cs (fun _ => blank) K 0 pk)
      (2*(V.length+W.length+U.length+T.length+D.length)+25) := by
  have h1 := clearV V W U X T D cs hs (CountedLateRepairFlag.key fl) K 0 pk
  have h2 := clearW [] W U X T D cs hs (CountedLateRepairFlag.key fl) K 0 pk
  have h3 := clearU [] [] U X T D cs hs (CountedLateRepairFlag.key fl) K 0 pk
  have h4 := clearT [] [] [] X T D cs hs (CountedLateRepairFlag.key fl) K 0 pk
  have h5 := clearD [] [] [] X [] D cs hs (CountedLateRepairFlag.key fl) K 0 pk
  have h6 := clearF [] [] [] X [] [] cs hs fl K pk
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank [] [] [] X [] [] hs cs (fun _ => blank)
    (FlagCopy.keyTape (FlagCopy.keyWord (fl q b V W U X) (bits q b hb hbq V W U X))) 0 0

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    HoareTime program (fun v => v=written q b hb hbq V W U X cs hs)
      (fun v => v=output q b hb hbq V W U X cs hs) (40*((X.length+1)*(q+b+1))) := by
  have h := runs_words (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X (target q b hb hbq V W U X) (dirty q b hb hbq V W U X) cs hs (fl q b V W U X)
    (FlagCopy.keyTape (FlagCopy.keyWord (fl q b V W U X) (bits q b hb hbq V W U X))) 0
  obtain ⟨_,_,_,hu,ht,hw⟩ := CountedLateRepairInverse.lengths q b hb hbq V W U X hV hW hU
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [target,CountedIdealToggle.word_length q _ X (by omega) (ht.trans hV),dirty,List.length_append,ht,hw,hu,hV,hW,hU]
  nlinarith

end
end IntegerMultBounds.Machine.CountedLateRepairKeyCleanup
