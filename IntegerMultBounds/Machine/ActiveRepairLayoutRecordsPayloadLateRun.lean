import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateData

/-! Actual original later payload execution, clean full-width repair and
physical copy-back share the original array tape. Every private tape is blank
at entry and exit, and every original numeric word is retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixDirtyControlConjugationData (FullArray Kind)
open ActiveRepairLayoutRecordsPayloadLateData
open ActivePrefixDirtyControlSequenceOriginalRun (count)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def lowProgramFor (a b c e : Kind) := ActiveRepairLayoutRecordsPayloadLatePlaced.programFor a b c e focus focus_injective
def repairProgram := extend (extend ActiveRepairLayoutRecordsCleanAlphabet.Late.program 8) count
def recycleProgram := extend
  (ActiveRepairArrayRecycle.program (232:Fin 252) 237 (by decide) (by decide) prime) count
def programFor (a b c e : Kind) := seq (seq (lowProgramFor a b c e) repairProgram) recycleProgram
def program := programFor .tPure .tNegative .uPure .uNegative

def input (d : Inputs s p offset rows) (x : FullArray s rows) := CleanSubbank.bank (s:=count) (caller d x)
def output (d : Inputs s p offset rows) (x : FullArray s rows) := CleanSubbank.bank (s:=count) (caller d (ideal d x))
def repairConstant (D : ℕ) := ActiveRepairLayoutRecordsHeadersAfterBudget.constant+
  ActiveRepairLateOriginalPipelineBudget.volumeConstant D+ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+1017
def costFor (a b c e : Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (D : ℕ) :=
  ActivePrefixDirtyControlSequenceOriginalRun.costFor a b c e hfit hn hb d+1+
    repairConstant D*(rows*s.recordWidth)+1+(5*(rows*s.recordWidth)+10)
def cost (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (D : ℕ) := costFor .tPure .tNegative .uPure .uNegative hfit hn hb d D

theorem actual_result (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) :
    ActivePrefixDirtyControlSequenceRun.laterFor .tPure .tNegative .uPure .uNegative
      (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x=actual d x :=
  ActiveRepairLayoutRecordsLate.result_move s p offset rows hfit hn hb d.hrecord d.hr d.hK d.hd d.hg x

theorem runs_for (a b c e : Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows)
    (hactual : ActivePrefixDirtyControlSequenceRun.laterFor a b c e
      (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x=actual d x)
    (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (programFor a b c e) (fun v => v=input d x) (fun v => v=output d x)
      (costFor a b c e hfit hn hb d D) := by
  have hl := ActiveRepairLayoutRecordsPayloadLatePlaced.runs_for a b c e hfit hn hb
    (caller d x) focus focus_injective d x (caller_sources d x)
  have hm : SharedPlacementAlphabet.setTape (caller d x) (focus 22)
      (ActiveTargetRotation.word (ActivePrefixDirtyControlSequenceRun.laterFor a b c e
        (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x)) 0=caller d (actual d x) := by
    rw [hactual]
    exact caller_set d x (actual d x)
  have hl' := hl.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=count)) hm)) le_rfl
  have hr := hoare_extend_eq (hoare_extend_eq
    (ActiveRepairLayoutRecordsCleanAlphabet.Late.runs_linear d x hfit hq3 d.hr hR D hdensity)
    (extra d)) (SharedBank.empty count prime)
  have hr' : HoareTime repairProgram
      (fun v => v=CleanSubbank.bank (s:=count) (caller d (actual d x)))
      (fun v => v=(repairOutput d x).append (SharedBank.empty count prime))
      (repairConstant D*(rows*s.recordWidth)) :=
    hr.consequence (fun _ h => h.trans (congrArg
      (fun v => v.append (SharedBank.empty count prime)) (repair_input d x))) (fun _ h => h) le_rfl
  have hc := hoare_extend_eq (recycle_runs d x hfit hq3) (SharedBank.empty count prime)
  exact (hl'.seq hr').seq hc

theorem runs (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d x) (fun v => v=output d x) (cost hfit hn hb d D) :=
  runs_for .tPure .tNegative .uPure .uNegative hfit hn hb d x (actual_result hfit hn hb d x) hq3 hR D hdensity

theorem raw_output (d : Inputs s p offset rows) (x : FullArray s rows) :
    (output d x).tape (Fin.castAdd count (237:Fin 252))=ActiveTargetRotation.word (ideal d x) := rfl


def slots (i : Fin 23) : Fin (252+count) := Fin.castAdd count (focus i)

theorem slots_injective : Function.Injective slots :=
  (Fin.castAdd_injective _ _).comp focus_injective

theorem input_payload (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.payload (input d x) slots=ActiveRepairLayoutRecordsPayloadLatePlaced.common d x :=
  (append_payload (u:=count) (caller d x)).trans (caller_sources d x)

theorem input_private_blank (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.strip (input d x) slots=SharedBank.empty (252+count) prime :=
  bank_clean d x

theorem output_payload (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.payload (output d x) slots=ActiveRepairLayoutRecordsPayloadLatePlaced.common d (ideal d x) := by
  exact (append_payload (u:=count) (caller d (ideal d x))).trans (caller_sources d _)

theorem all_private_blank (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.strip (output d x) slots=SharedBank.empty (252+count) prime :=
  bank_clean d (ideal d x)

theorem private_blank (d : Inputs s p offset rows) (x : FullArray s rows) :
    SharedBank.payload (output d x) (Fin.natAdd 252)=SharedBank.empty count prime := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [output,CleanSubbank.bank,Tapes.append,SharedBank.empty]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateRun
