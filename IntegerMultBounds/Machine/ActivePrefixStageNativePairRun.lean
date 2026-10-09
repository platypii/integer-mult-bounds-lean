import IntegerMultBounds.Machine.ActivePrefixStageNativePairData
import IntegerMultBounds.Machine.BinaryPairFrame

/-! A literal basis instruction saves its incoming headers, rewrites the pair,
runs the real native stage, and physically restores the incoming pair. The
native payload is canonical row-major throughout; no view equality is assumed. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open ActivePrefixStageNativePairData (count focus focus_injective headers)
open ActivePrefixStagePairData (changePair pairWords)
open Networks.Shared50ModularControl (prime)
open Networks.BinaryRowProgram (Op)
variable {s : Shape} {B : ℕ}

def originalOp (d : Inputs s) : Op (Fin d.stage.slots) :=
  ⟨d.stage.target,d.stage.source,d.stage.distinct.symm⟩

theorem restore_input (d : Inputs s) (op : Op (Fin d.stage.slots)) :
    changePair (changePair d op) (originalOp d)=d := by
  cases d
  rfl

theorem restores (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs : Rows d B) :
    BinaryPairFrame.restoredPair focus (pairWords d)
      (ActivePrefixStageNativeRows.bank (changePair d op) xs)=ActivePrefixStageNativeRows.bank d xs := by
  have h := ActivePrefixStageNativePairData.bank_pair (changePair d op) (originalOp d) xs
  exact h

def coreProgram {q M : ℕ} (P : Program count q prime) (op : Op (Fin M)) :=
  seq (ActivePrefixStageNativePairData.program op) P

def program {q M : ℕ} (P : Program count q prime) (op : Op (Fin M)) :=
  BinaryPairFrame.program focus (coreProgram P op)

def bank (d : Inputs s) (xs : Rows d B) :=
  (ActivePrefixStageNativeRows.bank d xs).append (SharedBank.empty 1 prime)

def action (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs : Rows d B) : Rows d B :=
  ActivePrefixStageNativeRows.action (changePair d op) xs

def cost (d : Inputs s) (op : Op (Fin d.stage.slots)) (stageCost : ℕ) :=
  BinaryPairFrame.cost focus (pairWords d) (pairWords (changePair d op))
    (ActivePrefixStageNativePairData.cost d op+stageCost+1)

theorem runs_for {q : ℕ} (P : Program count q prime)
    (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs ys : Rows d B) (stageCost : ℕ)
    (h : HoareTime P (fun w => w=ActivePrefixStageNativeRows.bank (changePair d op) xs)
      (fun w => w=ActivePrefixStageNativeRows.bank (changePair d op) ys) stageCost) :
    HoareTime (program P op) (fun w => w=bank d xs) (fun w => w=bank d ys) (cost d op stageCost) := by
  have hc : HoareTime (coreProgram P op)
      (fun w => w=ActivePrefixStageNativeRows.bank d xs)
      (fun w => w=ActivePrefixStageNativeRows.bank (changePair d op) ys)
      (ActivePrefixStageNativePairData.cost d op+stageCost+1) :=
    ((ActivePrefixStageNativePairData.runs d op xs).seq h).consequence
    (fun _ h => h) (fun _ h => h) (by omega)
  have hf := BinaryPairFrame.runs focus focus_injective (coreProgram P op)
    _ _ (pairWords d) (pairWords (changePair d op)) _ (headers d xs) (headers (changePair d op) ys) hc
  rw [restores] at hf
  exact hf

/-- One actual native stage supplies every literal instruction wrapper.
The execution premise in the framing helper is discharged here by the proved
encode/stage/decode machine, independently of widths and coefficient arrays. -/
theorem exists_stage_program : ∃ q, ∃ P : Program count q prime,
    ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (op : Op (Fin d.stage.slots))
      (_hcode : s.payload=B*3+0) (xs : Rows d B) (_hn : ∀ i j,xs i j≠blank)
      (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D),
      HoareTime (program P op) (fun w => w=bank d xs) (fun w => w=bank d (action d op xs))
        (cost d op (ActivePrefixStageNative.cost (B:=B) D (changePair d op) hp)) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNativeRows.exists_program
  refine ⟨q,P,?_⟩
  intro D s B d op hcode xs hn hp
  exact runs_for P d op xs _ _ (hP D s B (changePair d op) hcode xs hn hp)

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairRun
