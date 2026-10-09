import IntegerMultBounds.Machine.ActiveRepairRecordFlattenPrepare

/-! Complete decoder from the literal unmarked record word. Its marker is
physically installed, consumed by cleanup, and absent from the final bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFlattenOriginal
noncomputable section
open ActiveRepairRecordFlatten ActiveRepairRecordFlattenEndpoint
open SharedPlacementAlphabet (setTape)

def input (rs : List Partition.Record) : Tapes 2 1 :=
  (cfg (putWord (fun _ => blank) 0 (encode rs)) (fun _ => blank) 0 0 0).tapes
def markerProgram := atProgram ActiveRepairRecordFlattenPrepare.program 0
def program := seq markerProgram ActiveRepairRecordFlattenEndpoint.program
def cost (rs : List Partition.Record) := 3+ActiveRepairRecordFlattenEndpoint.cost rs

theorem initialized (rs : List Partition.Record) :
    setTape (input rs) 0 (CountedTapeRepairCleanupWord.marked (encode rs)) 0=
      ActiveRepairRecordFlattenEndpoint.input rs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prepare (rs : List Partition.Record) :
    HoareTime markerProgram (fun v => v=input rs)
      (fun v => v=ActiveRepairRecordFlattenEndpoint.input rs) 2 := by
  have h := at_runs ActiveRepairRecordFlattenPrepare.program (input rs) 0 _ _ _ _ rfl rfl
    (ActiveRepairRecordFlattenPrepare.runs (putWord (fun _ => blank) 0 (encode rs)))
  rw [ActiveRepairRecordFlattenPrepare.marked_word,initialized] at h
  exact h

theorem runs (rs : List Partition.Record) :
    HoareTime program (fun v => v=input rs)
      (fun v => v=ActiveRepairRecordFlattenEndpoint.output rs) (cost rs) :=
  ((prepare rs).seq (ActiveRepairRecordFlattenEndpoint.runs rs)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem runs_linear (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r∈rs,r.payload.length≤R) :
    HoareTime program (fun v => v=input rs)
      (fun v => v=ActiveRepairRecordFlattenEndpoint.output rs) (5*rs.length*(R+1)+12) :=
  ((prepare rs).seq (ActiveRepairRecordFlattenEndpoint.runs_linear rs R hw)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActiveRepairRecordFlattenOriginal
