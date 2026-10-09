import IntegerMultBounds.Machine.ActiveRepairLateFieldsBank

/-! Actual paid copies, later exceptional guard, unrestricted inverse and
ideal toggle, retaining the genuine full scan counter throughout. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsRun
noncomputable section
open ActiveRepairLateFieldsBank

theorem copy_runs (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    HoareTime copyProgram (fun z => z=before V W U X cs hs)
      (fun z => z=loaded V W U X cs hs) (3*(V.length+W.length+U.length)+20) := by
  have h1 := ActiveRepairLateFieldsCopy.runs (before V W U X cs hs) 31 0 (by decide) (by decide)
    V rfl rfl rfl rfl
  have h2 := ActiveRepairLateFieldsCopy.runs (copiedV V W U X cs hs) 32 1 (by decide) (by decide)
    W rfl rfl rfl rfl
  have h3 := ActiveRepairLateFieldsCopy.runs (copiedW V W U X cs hs) 33 2 (by decide) (by decide)
    U rfl rfl rfl rfl
  rw [copied_eq] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem bank_assoc (v : Tapes 30 1) (V W U cs : List Bool) :
    bank v [] V W U cs = v.append
      ((FiniteReturnStack.bank (CountedGuardGadgetRecord.word []) 0).append (originals V W U cs)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem inverse_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime inverseProgram (fun z => z=loaded V W U X cs hs)
      (fun z => z=inverted q b hb hbq V W U X cs hs) (9005*((X.length+1)*(q+b+1))) := by
  have h := hoare_extend_eq
    (CountedLateRepairPrefix.runs (a := 1) q b hb hbq hbq3 V W U X hs hV hW hU hv hc)
    ((FiniteReturnStack.bank (CountedGuardGadgetRecord.word []) 0).append (originals V W U cs))
  unfold loaded inverted
  rw [bank_assoc,bank_assoc]
  exact h

theorem toggle_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime toggleProgram (fun z => z=inverted q b hb hbq V W U X cs hs)
      (fun z => z=toggled q b hb hbq V W U X cs hs) (533*((X.length+1)*(q+b+1))) := by
  exact hoare_extend_eq (CountedLateRepairToggle.runs q b hb hbq V W U X hs hV hW hU hv hc)
    (originals V W U cs)

def program := seq (seq copyProgram inverseProgram) toggleProgram

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=before V W U X cs hs)
      (fun z => z=toggled q b hb hbq V W U X cs hs) (9600*((X.length+1)*(q+b+1))) := by
  have h1 := copy_runs V W U X cs hs
  have h2 := inverse_runs q b hb hbq hbq3 V W U X cs hs hV hW hU hv hc
  have h3 := toggle_runs q b hb hbq V W U X cs hs hV hW hU hv hc
  refine ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) ?_
  rw [hV,hW,hU]
  nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsRun
