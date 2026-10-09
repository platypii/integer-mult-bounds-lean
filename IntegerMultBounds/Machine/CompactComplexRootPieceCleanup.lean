import IntegerMultBounds.Machine.CompactComplexRootPieceEntry
import IntegerMultBounds.Machine.BinaryDescriptorQueueCleanup

/-! Paid exit of the root-piece controller. The completed digit queue is
physically erased and restored to head zero, then all four generated numeric
headers are erased. The entire appended native/stack bank is retained. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceCleanup
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open CompactComplexRecursiveGeometry (arity)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def schedule : List CompactChildHeadersArithmetic.Op :=
  [.existing (.command (.erase 0)),.existing (.command (.erase 1)),
    .existing (.command (.erase 2)),.existing (.command (.erase 3))]
def cleared (st : State) := Function.update (Function.update (Function.update (Function.update st 0 none) 1 none) 2 none) 3 none

def queueProgram := CompactComplexRootPieceEntry.queueProgram (BinaryDescriptorQueueCleanup.program (a := a))
def program : Σ k, Program (43+(1+t)) k a :=
  ⟨_,seq (CompactComplexControllerTapeAssoc.program (extend queueProgram t))
    (extend (CompactChildHeadersArithmetic.compile schedule).2 (1+t))⟩

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem queue_runs (st : State) (ds : List ℕ) :
    HoareTime (queueProgram (a := a))
      (fun v => v=(bank st).append (FiniteReturnStack.bank (CompactComplexRootPieceController.queue ds)
        (1+(CompactComplexRootDigits.fields (a := a) ds).length)))
      (fun v => v=(bank st).append (FiniteReturnStack.bank (fun _ => blank) 0))
      (3*(CompactComplexRootDigits.fields (a := a) ds).length+13) := by
  have h := Placement.hoare_at (BinaryDescriptorQueueCleanup.fields_runs (a := a) ds)
    CompactComplexRootPieceEntry.queuePlacement
    ((bank st).append (FiniteReturnStack.bank (CompactComplexRootPieceController.queue ds)
      (1+(CompactComplexRootDigits.fields (a := a) ds).length))) (by
        rw [CompactComplexRootPieceEntry.queuePlacement,FiniteReturnStackAt.active_bank]
        rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,hw,rfl⟩
  rw [hw]
  change Placement.replace CompactComplexRootPieceEntry.queuePlacement _
    (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [CompactComplexRootPieceEntry.queuePlacement,FiniteReturnStackAt.replace_bank]
  change setTape _ (Fin.natAdd 43 (0 : Fin 1)) (fun _ => blank) 0=_
  rw [setTape_append_right]
  apply congrArg ((bank (a := a) st).append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem numeric_runs (st : State) (e left width : ℕ)
    (h0 : st 0=some 0) (h1 : st 1=some e) (h2 : st 2=some left) (h3 : st 3=some width) :
    HoareTime (CompactChildHeadersArithmetic.compile (a := a) schedule).2
      (fun v => v=bank st) (fun v => v=bank (cleared st))
      (100*(e+left+width+4)+4) := by
  have hv : CompactChildHeadersArithmetic.validSchedule schedule st := by
    simp [schedule,CompactChildHeadersArithmetic.validSchedule,CompactChildHeadersArithmetic.valid,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,h0,h1,h2,h3,Function.update]
  have he : CompactChildHeadersArithmetic.execute schedule st=cleared st := rfl
  have hc : CompactChildHeadersArithmetic.scheduleCost schedule st=100*(e+left+width+4)+4 := by
    simp [schedule,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,h0,h1,h2,h3,Function.update]
    omega
  have h := CompactChildHeadersArithmetic.schedule_runs (a := a) schedule st hv
  simpa only [he,hc] using h

private theorem final_cleared (ds : List ℕ) :
    cleared (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) ds ds.length)=
      CompactComplexRootDigitsFromHeader.emptyState := by
  funext i
  by_cases h0 : i=0
  · subst i; simp [cleared,Function.update,CompactComplexRootDigitsFromHeader.emptyState]
  by_cases h1 : i=1
  · subst i; simp [cleared,Function.update,CompactComplexRootDigitsFromHeader.emptyState]
  by_cases h2 : i=2
  · subst i; simp [cleared,Function.update,CompactComplexRootDigitsFromHeader.emptyState]
  by_cases h3 : i=3
  · subst i; simp [cleared,Function.update,CompactComplexRootDigitsFromHeader.emptyState]
  simp [cleared,CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put,
    CompactComplexRootDigits.state,CompactComplexRootDigitsFromHeader.emptyState,Function.update,h0,h1,h2,h3]

/-- Exactly the original fresh controller bank is returned, including queue
head zero and every obsolete numeric descriptor cell. -/
theorem runs (ds : List ℕ) (tail : Tapes t a) :
    HoareTime (program (a := a) (t := t)).2
      (fun v => v=CompactComplexRootPieceController.input (CompactComplexRootDigits.state 0) ds ds.length tail)
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 tail)
      (3*(CompactComplexRootDigits.fields (a := a) ds).length+18+
        100*(ds.length+CompactComplexRootPieceVisits.preceding ds+arity^ds.length+4)) := by
  let st := CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) ds ds.length
  have hq := CompactComplexControllerTapeAssoc.hoare (hoare_extend_eq (queue_runs (a := a) st ds) tail)
  have hn := hoare_extend_eq (numeric_runs (a := a) st ds.length
    (CompactComplexRootPieceVisits.preceding ds) (arity^ds.length)
    (by simp [st,CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put,CompactComplexRootDigits.state])
    (by simp [st,CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put])
    (by simp [st,CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put])
    (by simp [st,CompactComplexRootPieceController.state,CompactComplexRootPieceController.ready,put]))
    ((FiniteReturnStack.bank (fun _ => blank) 0).append tail)
  rw [show cleared st=CompactComplexRootDigitsFromHeader.emptyState from final_cleared ds] at hn
  have hp : CompactComplexRootPieceController.cursor ds ds.length=
      1+(CompactComplexRootDigits.fields (a := a) ds).length := by
    simp [CompactComplexRootPieceController.cursor,CompactComplexRootDigits.fields]
  have h := hq.seq hn
  apply h.consequence
  · rintro v hv
    simpa only [CompactComplexRootPieceController.input,CompactComplexRootPieceDigit.input,hp] using hv
  · intro v hv; exact hv
  · omega

end
end IntegerMultBounds.Machine.CompactComplexRootPieceCleanup
