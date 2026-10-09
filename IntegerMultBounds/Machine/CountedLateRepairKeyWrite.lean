import IntegerMultBounds.Machine.CountedLateRepairKeyPrefix

/-! The conditional writer physically emits the later destination bits,
using the paid concatenation of its two recovered dirty words. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyWrite
noncomputable section
open CountedLateRepairKeyBank
open CountedRankSplitBank (placed_exact)

theorem input_view (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool) (fl : Bool) :
    Placement.active writePlace (bank V W U X T D hs cs (CountedLateRepairFlag.key fl) (FlagCopy.keyTape []) 1 0)=
      CountedRepairKeyAppend.input fl T D := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem output_view (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool) (fl : Bool) :
    Placement.active writePlace (bank V W U X T D hs cs (CountedLateRepairFlag.key fl)
      (FlagCopy.keyTape (FlagCopy.keyWord fl (T++D))) 0 0)=CountedRepairKeyAppend.output fl T D := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem extra_index (i : Fin 30) : writePlace (Fin.natAdd 4 i)=![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,29,30] i := by
  fin_cases i <;> decide

theorem extra_view (V W U X T D cs : List Bool) (hs : Fin 3 → List Bool)
    (F1 F2 K1 K2 : ℤ → Fin 5) (pf1 pf2 pk1 pk2 : ℤ) :
    Placement.extra writePlace (bank V W U X T D hs cs F1 K1 pf1 pk1)=
      Placement.extra writePlace (bank V W U X T D hs cs F2 K2 pf2 pk2) := by
  unfold Placement.extra
  apply congrArg₂ Tapes.mk <;> funext i <;> rw [extra_index]
  all_goals fin_cases i <;> rfl

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    HoareTime writeProgram (fun v => v=concatenated q b hb hbq V W U X cs hs)
      (fun v => v=written q b hb hbq V W U X cs hs) (30*((X.length+1)*(q+b+1))) := by
  have h : HoareTime writeProgram (fun v => v=concatenated q b hb hbq V W U X cs hs)
      (fun v => v=written q b hb hbq V W U X cs hs)
      (3*((target q b hb hbq V W U X).length+(dirty q b hb hbq V W U X).length)+18) :=
    placed_exact writePlace _ _ _ _ (input_view _ _ _ _ _ _ _ _ _)
      (output_view _ _ _ _ _ _ _ _ _) (extra_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (CountedRepairKeyAppend.runs (fl q b V W U X) (target q b hb hbq V W U X) (dirty q b hb hbq V W U X))
  obtain ⟨_,_,_,hu,ht,hw⟩ := CountedLateRepairInverse.lengths q b hb hbq V W U X hV hW hU
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [target,CountedIdealToggle.word_length q _ X (by omega) (ht.trans hV),dirty,List.length_append,hw,hu,hW,hU]
  nlinarith

def program := seq (seq (seq prefixProgram toggleProgram) concatProgram) writeProgram

theorem all_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=ranked V W U X cs hs)
      (fun v => v=written q b hb hbq V W U X cs hs) (9600*((X.length+1)*(q+b+1))) := by
  have h1 := CountedLateRepairKeyPrefix.prefix_runs q b hb hbq hbq3 V W U X cs hs hV hW hU hv hc
  have h2 := CountedLateRepairKeyPrefix.toggle_runs q b hb hbq V W U X cs hs hV hW hU hv hc
  have h3 := CountedLateRepairKeyPrefix.concat_runs q b hb hbq V W U X cs hs hV hW hU
  have h4 := runs q b hb hbq V W U X cs hs hV hW hU
  refine (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) ?_
  have hp : 1≤(X.length+1)*(q+b+1) :=
    Nat.mul_pos (by omega : 0<X.length+1) (by omega : 0<q+b+1)
  omega

end
end IntegerMultBounds.Machine.CountedLateRepairKeyWrite
