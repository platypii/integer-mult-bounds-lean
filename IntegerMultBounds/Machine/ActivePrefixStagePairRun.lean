import IntegerMultBounds.Machine.ActivePrefixStagePairData
import IntegerMultBounds.Machine.BinaryPairFrame

/-! Each fixed literal binary instruction saves its incoming pair, physically
rewrites the original headers, executes the complete runtime stage, and restores
the incoming descriptors. One private stack is blank at both endpoints. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStagePairData
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

abbrev count := ActivePrefixStageRuntimeProgram.count+1

def originalOp (d : Inputs s) : Op (Fin d.stage.slots) :=
  ⟨d.stage.target,d.stage.source,d.stage.distinct.symm⟩

theorem restore_input (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    changePair (changePair d op) (originalOp d)=d := by
  cases d
  rfl

theorem restores (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows) :
    BinaryPairFrame.restoredPair focus (pairWords d) (ActivePrefixStageRuntimeProgram.bank (changePair d op) x)=
      ActivePrefixStageRuntimeProgram.bank d x := by
  have h := bank_pair (changePair d op) (originalOp d) x
  exact h

def coreFor {M : ℕ} (op : Op (Fin M)) (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode) :=
  seq (ActivePrefixStagePairData.program op) (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
def programFor {M : ℕ} (op : Op (Fin M)) (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode) :=
  BinaryPairFrame.program focus (coreFor op a b c e m n r)
def program {M : ℕ} (op : Op (Fin M)) := programFor op .tPure .tNegative .uPure .uNegative .pure .pure .pure

def bank (d : Inputs s) (x : Array s d.rows) :=
  (ActivePrefixStageRuntimeProgram.bank d x).append (SharedBank.empty 1 prime)

def action (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows) :=
  ActivePrefixStageRuntimeData.result (changePair d op) x

def cost (d : Inputs s) (op : Op (Fin d.stage.slots)) (B : ℕ) :=
  BinaryPairFrame.cost focus (pairWords d) (pairWords (changePair d op)) (ActivePrefixStagePairData.cost d op+B+1)

theorem core_runs (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (op : Op (Fin d.stage.slots)) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank (changePair d op) x)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank (changePair d op) y) B) :
    HoareTime (coreFor op a b c e m n r)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank d x)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank (changePair d op) y) (ActivePrefixStagePairData.cost d op+B+1) :=
  ((ActivePrefixStagePairData.runs d op x).seq h).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (op : Op (Fin d.stage.slots)) (x y : Array s d.rows) (B : ℕ)
    (h : HoareTime (ActivePrefixStageRuntimeProgram.programFor a b c e m n r)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank (changePair d op) x)
      (fun w => w=ActivePrefixStageRuntimeProgram.bank (changePair d op) y) B) :
    HoareTime (programFor op a b c e m n r) (fun w => w=bank d x) (fun w => w=bank d y) (cost d op B) := by
  have hh := BinaryPairFrame.runs focus focus_injective (coreFor op a b c e m n r)
    _ _ (pairWords d) (pairWords (changePair d op)) _ (headers d x) (headers (changePair d op) y)
    (core_runs a b c e m n r d op x y B h)
  rw [restores] at hh
  exact hh

theorem runs (D : ℕ) (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D) :
    HoareTime (program op) (fun w => w=bank d x) (fun w => w=bank d (action d op x))
      (cost d op (ActivePrefixStageRuntimeData.cost D (changePair d op) hp)) :=
  runs_for .tPure .tNegative .uPure .uNegative .pure .pure .pure d op x _ _
    (ActivePrefixStageRuntimeRun.runs D (changePair d op) x hp)

end
end IntegerMultBounds.Machine.ActivePrefixStagePairRun
