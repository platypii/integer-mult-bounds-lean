import IntegerMultBounds.Networks.BoundedFramedCircuit
import IntegerMultBounds.Networks.Shared50FiniteTrace
import IntegerMultBounds.Networks.Shared50Finite
import IntegerMultBounds.Networks.DAGComplementExecution

/-! Actual finite-bank physical forward and complementary inverse execution.
All declared frame incidences, including scalar-empty identity pivots, are
restricted by proved bounds; no register or instruction is filtered out. -/

namespace IntegerMultBounds.Networks.Shared50FiniteFramed

open FramedCircuit BoundedFramedCircuit DisjointCircuit DAGSupportTrace

section Bounds
variable {α E : Type*} {h : ℕ} [AddCommGroup E] [Module (ZMod 2) E]

private theorem bounded_append (capacity : ℕ) (left right : List (Instruction ℕ (ZMod 2) E))
    (hl : Bounded capacity left) (hr : Bounded capacity right) : Bounded capacity (left ++ right) := by
  intro instr hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hl instr hi
  · exact hr instr hi

private theorem edges_bound (capacity : ℕ) (current desired : ℕ → Frame (ZMod 2) E)
    (wires : List ℕ) (hb : ∀ i ∈ wires, i < capacity) : Bounded capacity (edges current desired wires) := by
  induction wires generalizing current with
  | nil => simp [edges,Bounded]
  | cons i wires ih =>
    intro instr hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hb i (by simp)
    · exact ih _ (fun j hj => hb j (by simp [hj])) instr hi

private theorem gates_bound (capacity : ℕ) (program : Circuit.Program ℕ (ZMod 2))
    (hb : BoundedCircuit.Bounded capacity program) :
    Bounded capacity (program.map (Instruction.gate (E := E))) := by
  intro instr hi
  obtain ⟨gate,hg,rfl⟩ := List.mem_map.mp hi
  exact hb gate hg

private theorem forward_schedule_bound (capacity : ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) (es : List (Event α))
    (hl : ∀ event ∈ es, event.gate.HasLayout)
    (hb : ∀ event ∈ es, event.gate.Bounded capacity) (current : ℕ → Finset α) :
    Bounded capacity (DAGFramedExecution.schedule triples frameOf es current) := by
  induction es generalizing current with
  | nil => simp [DAGFramedExecution.schedule,Bounded]
  | cons event es ih =>
    apply bounded_append
    · apply bounded_append
      · exact edges_bound capacity _ _ _ (hb event (by simp))
      · exact gates_bound capacity _ (DAGFiniteCompile.gate_program_bounded capacity event.gate
          (hl event (by simp)) (hb event (by simp)))
    · exact ih (fun event he => hl event (by simp [he])) (fun event he => hb event (by simp [he])) _

private theorem undo_bound {L M : Type*} (capacity : ℕ) (dual : L → M) (xs : List (ℕ × L))
    (hb : ∀ p ∈ xs, p.1 < capacity) (current : ℕ → L) :
    ∀ p ∈ DAGComplementTrace.undo dual current xs, p.1 < capacity := by
  induction xs generalizing current with
  | nil => simp [DAGComplementTrace.undo]
  | cons p xs ih =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih (fun r hr => hb r (by simp [hr])) _ q hq
    · have he : q = (p.1,dual (current p.1)) := List.mem_singleton.mp hq
      simpa only [he] using hb p (by simp)

private theorem align_bound {L : Type*} (capacity : ℕ) (frameOf : L → Frame (ZMod 2) E)
    (xs : List (ℕ × L)) (hb : ∀ p ∈ xs, p.1 < capacity) (current : ℕ → L) :
    Bounded capacity (DAGComplementExecution.align frameOf current xs) := by
  induction xs generalizing current with
  | nil => simp [DAGComplementExecution.align,Bounded]
  | cons p xs ih =>
    intro instr hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hb p (by simp)
    · exact ih (fun q hq => hb q (by simp [hq])) _ instr hi

private theorem inverse_schedule_bound (capacity : ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) (es : List (Event α))
    (hl : ∀ event ∈ es, event.gate.HasLayout)
    (hb : ∀ event ∈ es, event.gate.Bounded capacity) (current : ℕ → Finset α) :
    Bounded capacity (DAGComplementExecution.schedule triples frameOf es current) := by
  induction es generalizing current with
  | nil => simp [DAGComplementExecution.schedule,Bounded]
  | cons event es ih =>
    apply bounded_append
    · exact ih (fun event he => hl event (by simp [he])) (fun event he => hb event (by simp [he])) _
    · apply bounded_append
      · exact gates_bound capacity _ (fun gate hg => DAGFiniteCompile.gate_program_bounded capacity event.gate
          (hl event (by simp)) (hb event (by simp)) gate (List.mem_reverse.mp hg))
      · apply align_bound
        apply undo_bound
        intro p hp
        obtain ⟨role,hr,he⟩ := List.mem_map.mp hp
        exact he ▸ hb event (by simp) role hr
end Bounds

open NeighborCounts SharedPointReplay
attribute [local irreducible] circuit

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private theorem event_bound (event : Event (Triple 50)) (he : event ∈ Shared50Frames.events) :
    event.gate.Bounded 509194 := by
  intro role hr
  have hm : (role, FanoutFrames.label (fun T : Triple 50 => T.val) event.support) ∈ Shared50Frames.updates :=
    List.mem_flatMap.mpr ⟨event,he,List.mem_map.mpr ⟨role,hr,rfl⟩⟩
  exact Shared50FiniteTrace.forward_bound _ hm

/-- Every physical forward instruction is bounded, including declared pivots
whose scalar program is empty. -/
theorem forward_bound (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    Bounded 509194 (DAGFramedExecution.forward circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf) :=
  forward_schedule_bound _ _ _ _ (events_layout circuit.nodes outputRefs valid outputRefs_bounds) event_bound _

/-- The complementary inverse retains and bounds every reversed alignment. -/
theorem inverse_bound (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    Bounded 509194 (DAGComplementExecution.inverse circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf) :=
  inverse_schedule_bound _ _ _ _ (events_layout circuit.nodes outputRefs valid outputRefs_bounds) event_bound _

/-- Actual physical forward instruction list on the certified finite side bank. -/
def forward (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) : List (Instruction (Fin 509194) (ZMod 2) E) :=
  restrict 509194 (DAGFramedExecution.forward circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf)
    (forward_bound frameOf)

/-- Actual physical complementary inverse instruction list on the same bank. -/
def inverse (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) : List (Instruction (Fin 509194) (ZMod 2) E) :=
  restrict 509194 (DAGComplementExecution.inverse circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf)
    (inverse_bound frameOf)

private theorem scalar_bound : BoundedCircuit.Bounded 509194 (DAGAllocator.compile circuit.nodes outputRefs).program :=
  DAGFiniteCompile.compile_program_bounded circuit.nodes outputRefs valid outputRefs_bounds 509194
    Shared50Certificate.role_bound

private theorem erase_eq (instructions : List (Instruction ℕ (ZMod 2) E)) :
    BoundedFramedCircuit.erase instructions = DAGFramedExecution.erase instructions := by
  simp only [BoundedFramedCircuit.erase,DAGFramedExecution.erase]
  congr 1
  funext instr
  cases instr <;> rfl

theorem forward_erasure (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    erase (forward frameOf) = Shared50Finite.program := by
  rw [forward,erase_restrict]
  change _ = BoundedCircuit.finiteProgram 509194 (DAGAllocator.compile circuit.nodes outputRefs).program scalar_bound
  apply finiteProgram_congr 509194 _ _ _ scalar_bound
  rw [erase_eq]
  exact DAGFramedExecution.forward_erasure circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf

theorem inverse_erasure (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E) :
    erase (inverse frameOf) = Shared50Finite.program.reverse := by
  rw [inverse,erase_restrict]
  change _ = (BoundedCircuit.finiteProgram 509194 (DAGAllocator.compile circuit.nodes outputRefs).program scalar_bound).reverse
  rw [← BoundedCircuit.finiteProgram_reverse]
  apply finiteProgram_congr 509194 _ _ _ (fun gate hg => scalar_bound gate (List.mem_reverse.mp hg))
  rw [erase_eq]
  exact DAGComplementExecution.inverse_erasure circuit.nodes outputRefs (fun T : Triple 50 => T.val) frameOf

/-- The actual finite physical forward execution on arbitrary module contents. -/
theorem forward_identity (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E)
    (stored : Fin 509194 → E) :
    FramedCircuit.run (forward frameOf) stored =
      encode (fun i => frameOf (Shared50Frames.finalLabels i.val))
        (moduleRun Shared50Finite.program
          (decode (fun i => frameOf (Shared50Frames.initialLabels i.val)) stored)) := by
  exact restrict_identity 509194 _ (forward_bound frameOf) _ scalar_bound _ _
    (DAGFramedExecution.forward_identity circuit.nodes outputRefs valid outputRefs_bounds
      (fun T : Triple 50 => T.val) frameOf) stored

/-- Complemented final frames decode the literal finite reversed computation;
complemented initial frames encode its physical result. -/
theorem inverse_identity (frameOf : Submodule ℚ (Fin 50 → ℚ) → Frame (ZMod 2) E)
    (stored : Fin 509194 → E) :
    FramedCircuit.run (inverse frameOf) stored =
      encode (fun i => frameOf ((Labels.rational 50).orthogonal (Shared50Frames.initialLabels i.val)))
        (moduleRun Shared50Finite.program.reverse
          (decode (fun i => frameOf ((Labels.rational 50).orthogonal (Shared50Frames.finalLabels i.val))) stored)) := by
  have hh := restrict_identity 509194 _ (inverse_bound frameOf) _
    (fun gate hg => scalar_bound gate (List.mem_reverse.mp hg)) _ _
    (DAGComplementExecution.inverse_identity circuit.nodes outputRefs valid outputRefs_bounds
      (fun T : Triple 50 => T.val) frameOf) stored
  rw [BoundedCircuit.finiteProgram_reverse] at hh
  exact hh

end IntegerMultBounds.Networks.Shared50FiniteFramed
