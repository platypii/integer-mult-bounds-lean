import IntegerMultBounds.Machine.SharedPayloadStage
import IntegerMultBounds.Machine.ExactFrame

/-! Actual sequential assembly of heterogeneous finite-state stages, keeping
exactly two shared payload tapes and retaining every private metadata bank. -/
namespace IntegerMultBounds.Machine.SharedPayloadStage
open SharedPlacementAlphabet (setTape setTape_append_left)
universe u
variable {X : Type u} {a t v : ℕ} {common : X → Tapes 2 a}

def emptyPair : Tapes 2 a := ⟨fun _ => 0,fun _ _ => blank⟩

theorem payload_two (w : Tapes 2 a) : SharedPayload.payload w 0 1 = w := by
  cases w with | mk head tape =>
    unfold SharedPayload.payload
    congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem strip_two (w : Tapes 2 a) : SharedPayload.strip w 0 1 = emptyPair := by
  have hh := SharedPayloadFrames.strip_payload w 0 1
  simpa only [payload_two,emptyPair] using hh

def source (t v : ℕ) : Fin ((2+t)+v) := Fin.castAdd v (Fin.castAdd t (0 : Fin 2))
def dest (t v : ℕ) : Fin ((2+t)+v) := Fin.castAdd v (Fin.castAdd t (1 : Fin 2))

theorem source_ne_dest (t v : ℕ) : source t v ≠ dest t v := by
  intro hh
  have hv := congrArg Fin.val hh
  simp [source,dest] at hv

theorem payload_append (w : Tapes 2 a) (left : Tapes t a) (right : Tapes v a) :
    SharedPayload.payload ((w.append left).append right) (source t v) (dest t v) = w := by
  simpa only [SharedPayload.payload,source,dest,Tapes.append,Fin.addCases_left]
    using payload_two w

theorem strip_append (w : Tapes 2 a) (left : Tapes t a) (right : Tapes v a) :
    SharedPayload.strip ((w.append left).append right) (source t v) (dest t v) =
      ((emptyPair.append left).append right) := by
  unfold SharedPayload.strip source dest
  rw [setTape_append_left,setTape_append_left,setTape_append_left,setTape_append_left]
  exact congrArg (fun z : Tapes 2 a => (z.append left).append right) (strip_two w)

/-- An actual zero-step terminal program, with no implicit head restoration. -/
def identity (common : X → Tapes 2 a) : Stage X a common where
  tapes := 2
  states := 1
  program := skip 2 a (by decide)
  transform := id
  input := common
  output := common
  source := 0
  dest := 1
  distinct := by decide
  metadata := emptyPair
  cost := 0
  input_payload := fun x => payload_two (common x)
  output_payload := fun x => payload_two (common x)
  strip_input := fun x => strip_two (common x)
  realizes := fun x => skip_hoare (by decide) (common x)

/-- Composition shares both payload tapes and supplies each private metadata
bank independently of the intermediate array. The join costs one transition. -/
noncomputable def compose (s r : Stage X a common) : Stage X a common where
  tapes := (2+s.tapes)+r.tapes
  states := s.states+r.states
  program := SharedPayloadPair.program s.program r.program s.source s.dest s.distinct r.source r.dest r.distinct
  transform := fun x => r.transform (s.transform x)
  input := fun x => SharedPayloadPair.input (s.input x) (r.input x) s.source s.dest r.source r.dest
  output := fun x => SharedPayloadPair.output (s.output x) (r.output (s.transform x)) s.source s.dest r.source r.dest
  source := source s.tapes r.tapes
  dest := dest s.tapes r.tapes
  distinct := source_ne_dest _ _
  metadata := (emptyPair.append s.metadata).append r.metadata
  cost := s.cost+r.cost+1
  input_payload := by
    intro x
    unfold SharedPayloadPair.input SharedPayload.bank
    rw [payload_append,s.input_payload]
  output_payload := by
    intro x
    unfold SharedPayloadPair.output
    rw [payload_append,r.output_payload]
  strip_input := by
    intro x
    unfold SharedPayloadPair.input SharedPayload.bank
    rw [strip_append,s.strip_input,r.strip_input]
  realizes := by
    intro x
    have hh := SharedPayloadPair.pair_hoare (s.realizes x) (r.realizes (s.transform x))
      s.source s.dest s.distinct r.source r.dest r.distinct
      (by rw [s.output_payload,r.input_payload])
    apply hh.consequence ?_ (fun _ h => h) le_rfl
    rintro w rfl
    unfold SharedPayloadPair.input
    rw [r.strip_input,r.strip_input]

/-- Structural recursion builds a finite-state machine for every finite list. -/
noncomputable def compile (common : X → Tapes 2 a) : List (Stage X a common) → Stage X a common
  | [] => identity common
  | s::ss => compose s (compile common ss)

def execute (ss : List (Stage X a common)) (x : X) : X := ss.foldl (fun y s => s.transform y) x

@[simp] theorem compile_transform (ss : List (Stage X a common)) (x : X) :
    (compile common ss).transform x = execute ss x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih (s.transform x)

/-- Every operation cost and every actual join to the terminal halt is paid. -/
theorem compile_cost (ss : List (Stage X a common)) :
    (compile common ss).cost = (ss.map Stage.cost).sum+ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change s.cost+(compile common ss).cost+1 = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- The final contract has no stage-runtime premise: it uses the concrete
program and correctness fields supplied by each actual stage constructor. -/
theorem compile_hoare (ss : List (Stage X a common)) (x : X) :
    HoareTime (compile common ss).program
      (fun v => v = (compile common ss).input x)
      (fun v => v = (compile common ss).output x ∧
        SharedPayload.payload v (compile common ss).source (compile common ss).dest = common (execute ss x))
      ((ss.map Stage.cost).sum+ss.length) := by
  rw [← compile_cost]
  apply ((compile common ss).realizes x).consequence (fun _ h => h) ?_ le_rfl
  rintro v rfl
  exact ⟨rfl,by rw [(compile common ss).output_payload,compile_transform]⟩

end IntegerMultBounds.Machine.SharedPayloadStage
