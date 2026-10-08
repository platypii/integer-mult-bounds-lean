import IntegerMultBounds.Machine.SharedBankStage

/-! Fixed finite control for the arbitrary-common-bank compiler. Erasing array
sizes, input words and contracts leaves a machine chosen solely by the schedule. -/
namespace IntegerMultBounds.Machine.SharedBankSkeleton
universe u

structure Skeleton (k alphabet : ℕ) where
  tapes : ℕ
  states : ℕ
  program : Program tapes states alphabet
  slots : Fin k → Fin tapes
  slots_injective : Function.Injective slots

variable {k a : ℕ} {X : Type u} {common : X → Tapes k a}
noncomputable section

def ofStage (s : SharedBankStage.Stage X k a common) : Skeleton k a :=
  ⟨s.tapes,s.states,s.program,s.slots,s.slots_injective⟩

def identity (k a : ℕ) (hk : 0 < k) : Skeleton k a where
  tapes := k
  states := 1
  program := skip k a hk
  slots := id
  slots_injective := Function.injective_id

def compose (s r : Skeleton k a) : Skeleton k a where
  tapes := (k+s.tapes)+r.tapes
  states := s.states+r.states
  program := SharedBankPair.program s.program r.program s.slots r.slots
  slots := SharedBankFrames.commonSlots k s.tapes r.tapes
  slots_injective := SharedBankFrames.commonSlots_injective _ _ _

def compile (k a : ℕ) (hk : 0 < k) : List (Skeleton k a) → Skeleton k a
  | [] => identity k a hk
  | s::ss => compose s (compile k a hk ss)

@[simp] theorem ofStage_identity (hk : 0 < k) :
    ofStage (SharedBankStage.identity common hk) = identity k a hk := rfl

@[simp] theorem ofStage_compose (s r : SharedBankStage.Stage X k a common) :
    ofStage (SharedBankStage.compose s r) = compose (ofStage s) (ofStage r) := rfl

theorem ofStage_compile (hk : 0 < k) (ss : List (SharedBankStage.Stage X k a common)) :
    ofStage (SharedBankStage.compile common hk ss) = compile k a hk (ss.map ofStage) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change compose (ofStage s) (ofStage (SharedBankStage.compile common hk ss)) =
      compose (ofStage s) (compile k a hk (ss.map ofStage))
    rw [ih]

/-- The same previously chosen program operates at every supported input size. -/
theorem fixed_program (s : SharedBankStage.Stage X k a common) (sk : Skeleton k a)
    (h : ofStage s = sk) :
    ∃ (input output : X → Tapes sk.tapes a) (metadata : Tapes sk.tapes a),
      (∀ x, SharedBank.payload (input x) sk.slots = common x) ∧
      (∀ x, SharedBank.strip (input x) sk.slots = metadata) ∧
      (∀ x, HoareTime sk.program (fun v => v = input x)
        (fun v => v = output x ∧ SharedBank.payload v sk.slots = common (s.transform x)) s.cost) := by
  subst sk
  refine ⟨s.input,s.output,s.metadata,s.input_payload,s.strip_input,?_⟩
  intro x
  apply (s.realizes x).consequence (fun _ h => h) ?_ le_rfl
  rintro v rfl
  exact ⟨rfl,s.output_payload x⟩

/-- A stronger transport for initialized stages: every private input tape is
blank at head zero; only the permanent common bank is supplied. -/
theorem fixed_program_blank (s : SharedBankStage.Stage X k a common) (sk : Skeleton k a)
    (h : ofStage s = sk) (hb : s.metadata = SharedBank.empty s.tapes a) :
    ∃ (input output : X → Tapes sk.tapes a),
      (∀ x, SharedBank.payload (input x) sk.slots = common x) ∧
      (∀ x, SharedBank.strip (input x) sk.slots = SharedBank.empty sk.tapes a) ∧
      (∀ x, HoareTime sk.program (fun v => v = input x)
        (fun v => v = output x ∧ SharedBank.payload v sk.slots = common (s.transform x)) s.cost) := by
  subst sk
  refine ⟨s.input,s.output,s.input_payload,?_,?_⟩
  · intro x; exact (s.strip_input x).trans hb
  · intro x
    apply (s.realizes x).consequence (fun _ h => h) ?_ le_rfl
    rintro v rfl
    exact ⟨rfl,s.output_payload x⟩

end
end IntegerMultBounds.Machine.SharedBankSkeleton
