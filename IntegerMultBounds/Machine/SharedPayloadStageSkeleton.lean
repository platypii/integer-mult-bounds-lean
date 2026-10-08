import IntegerMultBounds.Machine.SharedPayloadStageCompose

/-! Erasing array types and supplied descriptors from a concrete stage exposes
its fixed finite-state machine. The finite compiler depends only on this data. -/
namespace IntegerMultBounds.Machine.SharedPayloadStageSkeleton
universe u

structure Skeleton (alphabet : ℕ) where
  tapes : ℕ
  states : ℕ
  program : Program tapes states alphabet
  source : Fin tapes
  dest : Fin tapes
  distinct : source ≠ dest

variable {a : ℕ} {X : Type u} {common : X → Tapes 2 a}

def ofStage (s : SharedPayloadStage.Stage X a common) : Skeleton a :=
  ⟨s.tapes,s.states,s.program,s.source,s.dest,s.distinct⟩

def identity (a : ℕ) : Skeleton a where
  tapes := 2
  states := 1
  program := skip 2 a (by decide)
  source := 0
  dest := 1
  distinct := by decide

noncomputable def compose (s r : Skeleton a) : Skeleton a where
  tapes := (2+s.tapes)+r.tapes
  states := s.states+r.states
  program := SharedPayloadPair.program s.program r.program s.source s.dest s.distinct r.source r.dest r.distinct
  source := SharedPayloadStage.source s.tapes r.tapes
  dest := SharedPayloadStage.dest s.tapes r.tapes
  distinct := SharedPayloadStage.source_ne_dest _ _

noncomputable def compile (a : ℕ) : List (Skeleton a) → Skeleton a
  | [] => identity a
  | s::ss => compose s (compile a ss)

@[simp] theorem ofStage_identity : ofStage (SharedPayloadStage.identity common) = identity a := rfl

@[simp] theorem ofStage_compose (s r : SharedPayloadStage.Stage X a common) :
    ofStage (SharedPayloadStage.compose s r) = compose (ofStage s) (ofStage r) := rfl

/-- Finite compilation ignores array size, descriptors and proof contracts. -/
theorem ofStage_compile (ss : List (SharedPayloadStage.Stage X a common)) :
    ofStage (SharedPayloadStage.compile common ss) = compile a (ss.map ofStage) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change compose (ofStage s) (ofStage (SharedPayloadStage.compile common ss)) =
      compose (ofStage s) (compile a (ss.map ofStage))
    rw [ih]

/-- Transport to a previously chosen fixed program. Input and output remain
exact banks, and private initialization is independent of the input array. -/
theorem fixed_program (s : SharedPayloadStage.Stage X a common) (sk : Skeleton a)
    (h : ofStage s = sk) :
    ∃ (input output : X → Tapes sk.tapes a) (metadata : Tapes sk.tapes a),
      (∀ x, SharedPayload.payload (input x) sk.source sk.dest = common x) ∧
      (∀ x, SharedPayload.strip (input x) sk.source sk.dest = metadata) ∧
      (∀ x, HoareTime sk.program (fun v => v = input x)
        (fun v => v = output x ∧ SharedPayload.payload v sk.source sk.dest = common (s.transform x)) s.cost) := by
  subst sk
  refine ⟨s.input,s.output,s.metadata,s.input_payload,s.strip_input,?_⟩
  intro x
  apply (s.realizes x).consequence (fun _ h => h) ?_ le_rfl
  rintro v rfl
  exact ⟨rfl,s.output_payload x⟩

end IntegerMultBounds.Machine.SharedPayloadStageSkeleton
