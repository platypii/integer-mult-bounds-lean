import IntegerMultBounds.Machine.ActivePrefixStageNativePairRun

/-! A literal basis word compiles to a finite native machine. Every instruction
physically restores its pair headers and private frame, so each next stage reads
the same canonical row-major caller without coordinate-conversion premises. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open ActivePrefixStageNativePairRun (bank action)
open ActivePrefixStagePairData (changePair)
open Networks.Shared50ModularControl (prime)
open Networks.BinaryRowProgram (Op)
variable {s : Shape} {B : ℕ}

abbrev count := ActivePrefixStageNative.tapes+1
theorem positive_count : 0<count := Nat.zero_lt_succ _

def block {q M : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (op : Op (Fin M)) : Σ r,Program count r prime :=
  ⟨_,ActivePrefixStageNativePairRun.program P op⟩

def states {q M : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) : List (Op (Fin M)) → ℕ
  | [] => 1
  | op::ops => (block P op).1+states P ops

def program {q M : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) :
    (ops : List (Op (Fin M))) → Program count (states P ops) prime
  | [] => skip count prime positive_count
  | op::ops => seq (block P op).2 (program P ops)

def result (d : Inputs s) : List (Op (Fin d.stage.slots)) → Rows d B → Rows d B
  | [],xs => xs
  | op::ops,xs => result d ops (action d op xs)

theorem result_nonblank (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Rows d B) (hn : ∀ i j,xs i j≠blank) : ∀ i j,result d ops xs i j≠blank := by
  induction ops generalizing xs with
  | nil => exact hn
  | cons op ops ih => exact ih _ (ActivePrefixStageNativeRows.action_nonblank (changePair d op) xs hn)

def cost {M : ℕ} (bounds : Op (Fin M) → ℕ) (ops : List (Op (Fin M))) :=
  (ops.map (fun op => bounds op+1)).sum

theorem runs_for {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (d : Inputs s) (bounds : Op (Fin d.stage.slots) → ℕ)
    (hb : ∀ op (xs : Rows d B), (∀ i j,xs i j≠blank) →
      HoareTime (ActivePrefixStageNativePairRun.program P op)
        (fun w => w=bank d xs) (fun w => w=bank d (action d op xs)) (bounds op))
    (ops : List (Op (Fin d.stage.slots))) (xs : Rows d B) (hn : ∀ i j,xs i j≠blank) :
    HoareTime (program P ops) (fun w => w=bank d xs)
      (fun w => w=bank d (result d ops xs)) (cost bounds ops) := by
  induction ops generalizing xs with
  | nil => exact skip_hoare positive_count _
  | cons op ops ih =>
    have h := (hb op xs hn).seq (ih (action d op xs) (ActivePrefixStageNativeRows.action_nonblank (changePair d op) xs hn))
    exact h.consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

def stageCost (D : ℕ) (d : Inputs s)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
    (op : Op (Fin d.stage.slots)) :=
  ActivePrefixStageNativePairRun.cost d op (ActivePrefixStageNative.cost (B:=B) D (changePair d op) (hp op))

/-- One fixed actual native stage compiles every literal word. Both conversion
and header save/rewrite/restore costs are paid at every instruction, including
all sequencing transitions. -/
theorem exists_stage_program : ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime,
    ∀ (D : ℕ) (s : Shape) (B : ℕ) (d : Inputs s) (_hcode : s.payload=B*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (changePair d op) D)
      (ops : List (Op (Fin d.stage.slots))) (xs : Rows d B) (_hn : ∀ i j,xs i j≠blank),
      HoareTime (program P ops) (fun w => w=bank d xs)
        (fun w => w=bank d (result d ops xs)) (cost (stageCost (B:=B) D d hp) ops) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNativePairRun.exists_stage_program
  refine ⟨q,P,?_⟩
  intro D s B d hcode hp ops xs hn
  exact runs_for P d (stageCost (B:=B) D d hp)
    (fun op ys hy => hP D s B d op hcode ys hy (hp op)) ops xs hn

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule
