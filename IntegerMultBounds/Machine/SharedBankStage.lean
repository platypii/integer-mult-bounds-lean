import IntegerMultBounds.Machine.SharedBankPair
import IntegerMultBounds.Machine.SharedBankFrames
import IntegerMultBounds.Machine.ExactFrame

/-! Finite compilation with a fixed permanent bank of arbitrary size. Actual
stages supply their discharged contracts; initialized four-tape stages share
the sole payload pair and b/W pair and require only blank private storage. -/
namespace IntegerMultBounds.Machine.SharedBankStage
universe u

structure Stage (X : Type u) (k alphabet : ℕ) (common : X → Tapes k alphabet) where
  tapes : ℕ
  states : ℕ
  program : Program tapes states alphabet
  transform : X → X
  input : X → Tapes tapes alphabet
  output : X → Tapes tapes alphabet
  slots : Fin k → Fin tapes
  slots_injective : Function.Injective slots
  metadata : Tapes tapes alphabet
  cost : ℕ
  input_payload : ∀ x, SharedBank.payload (input x) slots = common x
  output_payload : ∀ x, SharedBank.payload (output x) slots = common (transform x)
  strip_input : ∀ x, SharedBank.strip (input x) slots = metadata
  realizes : ∀ x, HoareTime program (fun v => v = input x) (fun v => v = output x) cost

variable {X : Type u} {k a : ℕ} {common : X → Tapes k a}
noncomputable section

/-- Literal terminal halt; it changes no tape and resets no head. -/
def identity (common : X → Tapes k a) (hk : 0 < k) : Stage X k a common where
  tapes := k
  states := 1
  program := skip k a hk
  transform := id
  input := common
  output := common
  slots := id
  slots_injective := Function.injective_id
  metadata := SharedBank.empty k a
  cost := 0
  input_payload := fun x => SharedBankFrames.payload_identity (common x)
  output_payload := fun x => SharedBankFrames.payload_identity (common x)
  strip_input := fun x => SharedBankFrames.strip_identity (common x)
  realizes := fun x => skip_hoare hk (common x)

/-- All common tapes retain their physical identity across the actual join. -/
def compose (s r : Stage X k a common) : Stage X k a common where
  tapes := (k+s.tapes)+r.tapes
  states := s.states+r.states
  program := SharedBankPair.program s.program r.program s.slots r.slots
  transform := fun x => r.transform (s.transform x)
  input := fun x => SharedBankPair.input (s.input x) (r.input x) s.slots r.slots
  output := fun x => SharedBankPair.output (s.output x) (r.output (s.transform x)) s.slots r.slots
  slots := SharedBankFrames.commonSlots k s.tapes r.tapes
  slots_injective := SharedBankFrames.commonSlots_injective _ _ _
  metadata := ((SharedBank.empty k a).append s.metadata).append r.metadata
  cost := s.cost+r.cost+1
  input_payload := by
    intro x
    unfold SharedBankPair.input SharedBank.bank
    rw [SharedBankFrames.payload_common,s.input_payload]
  output_payload := by
    intro x
    unfold SharedBankPair.output
    rw [SharedBankFrames.payload_common,r.output_payload]
  strip_input := by
    intro x
    unfold SharedBankPair.input SharedBank.bank
    rw [SharedBankFrames.strip_common,s.strip_input,r.strip_input]
  realizes := by
    intro x
    have hh := SharedBankPair.pair_hoare (s.realizes x) (r.realizes (s.transform x))
      s.slots s.slots_injective r.slots r.slots_injective
      (by rw [s.output_payload,r.input_payload])
    apply hh.consequence ?_ (fun _ h => h) le_rfl
    rintro v rfl
    unfold SharedBankPair.input
    rw [r.strip_input,r.strip_input]

def compile (common : X → Tapes k a) (hk : 0 < k) : List (Stage X k a common) → Stage X k a common
  | [] => identity common hk
  | s::ss => compose s (compile common hk ss)

def execute (ss : List (Stage X k a common)) (x : X) : X := ss.foldl (fun y s => s.transform y) x

@[simp] theorem compile_transform (hk : 0 < k) (ss : List (Stage X k a common)) (x : X) :
    (compile common hk ss).transform x = execute ss x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih (s.transform x)

theorem compile_cost (hk : 0 < k) (ss : List (Stage X k a common)) :
    (compile common hk ss).cost = (ss.map Stage.cost).sum+ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change s.cost+(compile common hk ss).cost+1 = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Initialized stages compose to an input with literally blank private storage. -/
theorem compile_metadata_empty (hk : 0 < k) (ss : List (Stage X k a common))
    (hblank : ∀ s ∈ ss, s.metadata = SharedBank.empty s.tapes a) :
    (compile common hk ss).metadata = SharedBank.empty (compile common hk ss).tapes a := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change ((SharedBank.empty k a).append s.metadata).append (compile common hk ss).metadata = _
    rw [hblank s (by simp),ih (fun r hr => hblank r (by simp [hr])),
      SharedBankFrames.empty_append,SharedBankFrames.empty_append]
    rfl

/-- Exact complete output and common-state correctness, with every join paid. -/
theorem compile_hoare (hk : 0 < k) (ss : List (Stage X k a common)) (x : X) :
    HoareTime (compile common hk ss).program (fun v => v = (compile common hk ss).input x)
      (fun v => v = (compile common hk ss).output x ∧
        SharedBank.payload v (compile common hk ss).slots = common (execute ss x))
      ((ss.map Stage.cost).sum+ss.length) := by
  rw [← compile_cost hk]
  apply ((compile common hk ss).realizes x).consequence (fun _ h => h) ?_ le_rfl
  rintro v rfl
  exact ⟨rfl,by rw [(compile common hk ss).output_payload,compile_transform]⟩

end
end IntegerMultBounds.Machine.SharedBankStage
