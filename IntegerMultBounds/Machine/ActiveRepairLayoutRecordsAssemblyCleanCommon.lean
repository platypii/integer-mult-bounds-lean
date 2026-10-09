import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLate
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLateAfter

/-! Real fixed-many erasure of the retained consumer metadata. Placement
preserves every whole unselected tape; lengths are paid by original volume. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanCommon
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairLayoutRecordsBankHeaders ActiveRepairLayoutRecordsHeadersBudget
open ActiveRepairLayoutRecordsHeadersSchedule ActiveRepairRankHeadersCommands
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}
variable {t u : ℕ}

theorem append_zero (v : Tapes 15 1) : (SharedBank.empty 0 1).append v=v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [Fin.addCases]

def localProgram := FixedHeaderBankCopy.cleanup (t:=0) (n:=15) (a:=1) (by decide)

theorem local_runs (ws : Fin 15 → List Bool) :
    HoareTime localProgram (fun v => v=FixedHeaderBankCopy.headerBank ws)
      (fun v => v=SharedBank.empty 15 1) (FixedHeaderBankCopy.cleanupCost (t:=0) ws) := by
  have hh := FixedHeaderBankCopy.cleans (a:=1) (t:=0) (n:=15) (by decide) (SharedBank.empty 0 1) ws
  rw [append_zero,append_zero] at hh
  exact hh

def placement (focus : Fin 15 → Fin t) (hi : Function.Injective focus) (hsize : 15+u=t) :=
  InjectivePlacement.placement focus hi hsize
def program (focus : Fin 15 → Fin t) (hi : Function.Injective focus) (hsize : 15+u=t) :=
  Placement.placed localProgram (placement focus hi hsize)

theorem replace_empty (focus : Fin 15 → Fin t) (hi : Function.Injective focus)
    (hsize : 15+u=t) (v : Tapes t 1) :
    Placement.replace (placement focus hi hsize) v (SharedBank.empty 15 1)=SharedBank.strip v focus := by
  let e := placement focus hi hsize
  have hn (i : Fin u) : ¬∃ j,focus j=e (Fin.natAdd 15 i) := by
    rintro ⟨j,hj⟩
    have hh := (InjectivePlacement.active_slot focus hi hsize j).trans hj
    have hx := congrArg Fin.val (e.injective hh)
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hx
    omega
  unfold Placement.replace
  apply congrArg₂ Tapes.mk <;> funext k
  all_goals obtain ⟨x,rfl⟩ := e.surjective k
  all_goals induction x using (Fin.addCases (m:=15) (n:=u)) with
  | left i =>
    first
    | change (Placement.combine e (SharedBank.empty 15 1) (Placement.extra e v)).head (e (Fin.castAdd u i))=_
      rw [Placement.combine_head_active]
      simp only [SharedBank.empty,show ∃j,focus j=e (Fin.castAdd u i) from ⟨i,(InjectivePlacement.active_slot focus hi hsize i).symm⟩,ite_true]
    | change (Placement.combine e (SharedBank.empty 15 1) (Placement.extra e v)).tape (e (Fin.castAdd u i))=_
      rw [Placement.combine_tape_active]
      simp only [SharedBank.empty,show ∃j,focus j=e (Fin.castAdd u i) from ⟨i,(InjectivePlacement.active_slot focus hi hsize i).symm⟩,ite_true]
  | right i =>
    first
    | change (Placement.combine e (SharedBank.empty 15 1) (Placement.extra e v)).head (e (Fin.natAdd 15 i))=_
      rw [Placement.combine_head_extra]
      simp only [Placement.extra,hn i,ite_false]
    | change (Placement.combine e (SharedBank.empty 15 1) (Placement.extra e v)).tape (e (Fin.natAdd 15 i))=_
      rw [Placement.combine_tape_extra]
      simp only [Placement.extra,hn i,ite_false]

theorem runs (focus : Fin 15 → Fin t) (hi : Function.Injective focus) (hsize : 15+u=t)
    (v : Tapes t 1) (ws : Fin 15 → List Bool)
    (hv : SharedBank.payload v focus=FixedHeaderBankCopy.headerBank ws) :
    HoareTime (program focus hi hsize) (fun w => w=v) (fun w => w=SharedBank.strip v focus)
      (FixedHeaderBankCopy.cleanupCost (t:=0) ws) := by
  have hp : Placement.active (placement focus hi hsize) v=FixedHeaderBankCopy.headerBank ws := by
    rw [placement,InjectivePlacement.active_bank]
    exact hv
  have hh := Placement.hoare_at (local_runs ws) (placement focus hi hsize) v hp
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact replace_empty focus hi hsize v

theorem words_canonical (d : Inputs s p offset rows) :
    ∀i,GrowingCounterData.Canonical (words d i) := by
  intro i; fin_cases i <;> first | exact d.hc _ | exact RecursiveChildQuotientsConstant.bits_canonical _

def producerFocus : Fin 15 → Fin 28 := ![0,1,2,3,4,5,6,11,17,18,7,9,10,16,8]

theorem words_value (d : Inputs s p offset rows) :
    ∀i,Counter.value (words d i)=(ready d (producerFocus i)).getD 0 := by
  intro i
  fin_cases i
  all_goals simp only [words,Matrix.cons_val_succ']
  all_goals first
    | simpa [ready,finished,scanned,initial,put,Function.update,producerFocus]
        using d.hv _
    | simp [RecursiveChildQuotientsConstant.bits_value,ready,finished,put,Function.update,
        producerFocus]

theorem cost_linear (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.before) :
    FixedHeaderBankCopy.cleanupCost (t:=0) (words d)≤405*volume s rows := by
  have hV : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hv := ActiveRepairLayoutRecordsBankBudget.ready_bound d hrows hp hfit
  have hc := FixedHeaderBankCopy.cleanup_cost_linear (t:=0) (words d) (2*volume s rows+1)
    (by omega) (words_canonical d) (by intro i; rw [words_value]; exact hv _)
  exact hc.trans (by nlinarith)


theorem cost_linear_after (d : Inputs s p offset rows) (hrows : 0<rows) (hp : 0<s.payload)
    (hfit : offset+p.f*p.q≤p.after) :
    FixedHeaderBankCopy.cleanupCost (t:=0) (words d)≤405*volume s rows := by
  have hV : 0<volume s rows := by unfold volume Shape.recordWidth; positivity
  have hv := ActiveRepairLayoutRecordsBankAfterBudget.ready_bound d hrows hp hfit
  have hc := FixedHeaderBankCopy.cleanup_cost_linear (t:=0) (words d) (2*volume s rows+1)
    (by omega) (words_canonical d) (by intro i; rw [words_value]; exact hv _)
  exact hc.trans (by nlinarith)

theorem final_cost_absorb (C V P Q : ℕ) (hV : 0<V) (hP : P≤C*V) (hQ : Q≤405*V) :
    P+1+Q≤(C+406)*V := by nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanCommon
