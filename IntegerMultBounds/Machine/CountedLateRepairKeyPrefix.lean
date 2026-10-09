import IntegerMultBounds.Machine.CountedLateRepairKeyBank

/-! Paid later inverse, ideal toggle, dirty-word concatenation and conditional
key writing, all on the common fixed34 bank. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyPrefix
noncomputable section
open CountedLateRepairKeyBank
open CountedRankSplitBank (placed_exact)

theorem prefix_input (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    ranked V W U X cs hs=(CountedLateRepairGuard.before V W U X hs).append
      (⟨![1,0,0,0],![RepairScan.ctrTape cs,FlagCopy.keyTape [],fun _ => blank,fun _ => blank]⟩ : Tapes 4 1) := by
  have h := CountedLateRepairPrefix.bank_eq (a := 1) V W U X hs (fun _ => blank) (fun _ => blank) 0 0
  unfold ranked bank CountedLateRepairGuard.before
  rw [h]
  rfl

theorem prefix_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime prefixProgram (fun v => v=ranked V W U X cs hs)
      (fun v => v=inverted q b hb hbq V W U X cs hs) (9005*((X.length+1)*(q+b+1))) := by
  have h := hoare_extend_eq (CountedLateRepairPrefix.runs (a := 1) q b hb hbq hbq3 V W U X hs hV hW hU hv hc)
    (⟨![1,0,0,0],![RepairScan.ctrTape cs,FlagCopy.keyTape [],fun _ => blank,fun _ => blank]⟩ : Tapes 4 1)
  rw [← prefix_input] at h
  exact h

theorem toggle_active (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool) (fl : Bool)
    (K : ℤ → Fin 5) (pk : ℤ) :
    Placement.active togglePlace (bank V W U X T D hs cs (CountedLateRepairFlag.key fl) K 1 pk)=
      CountedLateRepairToggle.working V W U X T hs fl := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem toggle_extra_index (i : Fin 3) : togglePlace (Fin.natAdd 31 i)=![30,31,33] i := by
  fin_cases i <;> decide

theorem toggle_extra (V W U X T1 T2 D cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    Placement.extra togglePlace (bank V W U X T1 D hs cs F K pf pk)=
      Placement.extra togglePlace (bank V W U X T2 D hs cs F K pf pk) := by
  unfold Placement.extra
  apply congrArg₂ Tapes.mk <;> funext i <;> rw [toggle_extra_index]
  all_goals fin_cases i <;> rfl

theorem toggle_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime toggleProgram (fun v => v=inverted q b hb hbq V W U X cs hs)
      (fun v => v=toggled q b hb hbq V W U X cs hs) (533*((X.length+1)*(q+b+1))) := by
  exact placed_exact togglePlace _ _ _ _ (toggle_active _ _ _ _ _ _ _ _ _ _ _)
    (toggle_active _ _ _ _ _ _ _ _ _ _ _) (toggle_extra _ _ _ _ _ _ _ _ _ _ _ _ _)
    (CountedLateRepairToggle.runs q b hb hbq V W U X hs hV hW hU hv hc)

theorem concat_input (V W U X T cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    Placement.active concatPlace (bank V W U X T [] hs cs F K pf pk)=
      CountedLateRepairConcat.input W U := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem concat_output (V W U X T cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    Placement.active concatPlace (bank V W U X T (W++U) hs cs F K pf pk)=
      CountedLateRepairConcat.output W U := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem concat_extra_index (i : Fin 30) : concatPlace (Fin.natAdd 4 i)=![0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31,32] i := by
  fin_cases i <;> decide

theorem concat_extra (V W U X T D1 D2 cs : List Bool) (hs : Fin 3 → List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) :
    Placement.extra concatPlace (bank V W U X T D1 hs cs F K pf pk)=
      Placement.extra concatPlace (bank V W U X T D2 hs cs F K pf pk) := by
  unfold Placement.extra
  apply congrArg₂ Tapes.mk <;> funext i <;> rw [concat_extra_index]
  all_goals fin_cases i <;> rfl

theorem concat_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    HoareTime concatProgram (fun v => v=toggled q b hb hbq V W U X cs hs)
      (fun v => v=concatenated q b hb hbq V W U X cs hs) (20*((X.length+1)*(q+b+1))) := by
  have h : HoareTime concatProgram (fun v => v=toggled q b hb hbq V W U X cs hs)
      (fun v => v=concatenated q b hb hbq V W U X cs hs)
      (3*((CountedLateRepairInverse.temp q b hb hbq V W U X).length +
        (CountedLateRepairInverse.restored b hb U X).length)+10) := placed_exact concatPlace _ _ _ _ (concat_input _ _ _ _ _ _ _ _ _ _ _)
    (concat_output _ _ _ _ _ _ _ _ _ _ _) (concat_extra _ _ _ _ _ _ _ _ _ _ _ _ _)
    (CountedLateRepairConcat.runs (CountedLateRepairInverse.temp q b hb hbq V W U X)
      (CountedLateRepairInverse.restored b hb U X))
  obtain ⟨_,_,_,hu,_,hw⟩ := CountedLateRepairInverse.lengths q b hb hbq V W U X hV hW hU
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [hu,hw,hW,hU]
  nlinarith

end
end IntegerMultBounds.Machine.CountedLateRepairKeyPrefix
