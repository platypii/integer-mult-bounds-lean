import IntegerMultBounds.Machine.ActivePrefixStagePairRun

/-! A fixed chronological list of literal binary row additions is compiled to
one finite machine. Every instruction restores the original pair and the one
private stack, so list composition retains the exact common caller bank. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairSchedule
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStagePairRun (bank count action)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

theorem positive_count : 0<count := Nat.zero_lt_succ _

def blockFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    {M : ℕ} (op : Op (Fin M)) : Σ q,Program count q prime :=
  ⟨_,ActivePrefixStagePairRun.programFor op a b c e m n r⟩

def statesFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    {M : ℕ} : List (Op (Fin M)) → ℕ
  | [] => 1
  | op::ops => (blockFor a b c e m n r op).1+statesFor a b c e m n r ops

def programFor (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    {M : ℕ} : (ops : List (Op (Fin M))) → Program count (statesFor a b c e m n r ops) prime
  | [] => skip count prime positive_count
  | op::ops => seq (blockFor a b c e m n r op).2 (programFor a b c e m n r ops)

def program {M : ℕ} (ops : List (Op (Fin M))) :=
  programFor .tPure .tNegative .uPure .uNegative .pure .pure .pure ops

def result (d : Inputs s) : List (Op (Fin d.stage.slots)) → Array s d.rows → Array s d.rows
  | [],x => x
  | op::ops,x => result d ops (action d op x)

def cost {M : ℕ} (B : Op (Fin M) → ℕ) (ops : List (Op (Fin M))) :=
  (ops.map (fun op => B op+1)).sum

theorem runs_for (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (B : Op (Fin d.stage.slots) → ℕ)
    (hb : ∀ op x, HoareTime (ActivePrefixStagePairRun.programFor op a b c e m n r)
      (fun w => w=bank d x) (fun w => w=bank d (action d op x)) (B op))
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (programFor a b c e m n r ops) (fun w => w=bank d x)
      (fun w => w=bank d (result d ops x)) (cost B ops) := by
  induction ops generalizing x with
  | nil => exact skip_hoare positive_count _
  | cons op ops ih =>
    have h := (hb op x).seq (ih (action d op x))
    exact h.consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

def stageCost (D : ℕ) (d : Inputs s)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (op : Op (Fin d.stage.slots)) :=
  ActivePrefixStagePairRun.cost d op
    (ActivePrefixStageRuntimeData.cost D (ActivePrefixStagePairData.changePair d op) (hp op))

theorem runs (D : ℕ) (d : Inputs s)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (ops : List (Op (Fin d.stage.slots))) (x : Array s d.rows) :
    HoareTime (program ops) (fun w => w=bank d x) (fun w => w=bank d (result d ops x))
      (cost (stageCost D d hp) ops) :=
  runs_for .tPure .tNegative .uPure .uNegative .pure .pure .pure d (stageCost D d hp)
    (fun op x => ActivePrefixStagePairRun.runs D d op x (hp op)) ops x

end
end IntegerMultBounds.Machine.ActivePrefixStagePairSchedule
