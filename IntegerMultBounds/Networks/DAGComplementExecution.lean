import IntegerMultBounds.Networks.DAGComplementTrace

/-! Physical complementary inverse execution, retaining each allocated event.
Inverse scalar gates run in complemented forward node frames, then the exact
reverse alignment restores the complemented previous profile. -/

namespace IntegerMultBounds.Networks.DAGComplementExecution

open DisjointCircuit DAGSupportTrace FramedCircuit

section Alignment
variable {L E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Execute arbitrary label updates with the frame left by the previous update. -/
def align (frameOf : L → Frame (ZMod 2) E) :
    (ℕ → L) → List (ℕ × L) → List (Instruction ℕ (ZMod 2) E)
  | _, [] => []
  | current, (i,next)::rest =>
    .edge i (frameOf (current i)) (frameOf next) :: align frameOf (Function.update current i next) rest

theorem align_invariant (frameOf : L → Frame (ZMod 2) E) (current : ℕ → L)
    (xs : List (ℕ × L)) (x : ℕ → E) :
    FramedCircuit.run (align frameOf current xs) (encode (fun i => frameOf (current i)) x) =
      encode (fun i => frameOf (RankTrace.finish current xs i)) x := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,next⟩ := p
    rw [align,FramedCircuit.run_cons,edge_invariant (fun j => frameOf (current j)) (frameOf next) i x]
    have he : Function.update (fun j => frameOf (current j)) i (frameOf next) =
        fun j => frameOf (Function.update current i next j) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [he,ih]
    rfl

theorem erase_align (frameOf : L → Frame (ZMod 2) E) (current : ℕ → L) (xs : List (ℕ × L)) :
    DAGFramedExecution.erase (align frameOf current xs) = [] := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,next⟩ := p
    simpa only [align,DAGFramedExecution.erase,List.filterMap_cons] using
      ih (Function.update current i next)
end Alignment

section Events
variable {α E : Type*} {h : ℕ} [AddCommGroup E] [Module (ZMod 2) E]

def dualLabels (triples : α → Finset (Fin h)) (current : ℕ → Finset α) :
    ℕ → Submodule ℚ (Fin h → ℚ) :=
  fun i => (Labels.rational h).orthogonal (FanoutFrames.label triples (current i))

def eventUndo (event : Event α) (triples : α → Finset (Fin h)) (current : ℕ → Finset α) :
    List (ℕ × Submodule ℚ (Fin h → ℚ)) :=
  DAGComplementTrace.undo (Labels.rational h).orthogonal
    (fun i => FanoutFrames.label triples (current i)) (event.updates triples)

/-- Reverse the literal scalar gate first in the complemented node frame;
then undo its declared alignment, including the zero-instruction pivot case. -/
def eventInverse (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) : List (Instruction ℕ (ZMod 2) E) :=
  event.gate.program.reverse.map Instruction.gate ++
    align frameOf (dualLabels triples (event.after current)) (eventUndo event triples current)

theorem event_undo_finish (event : Event α) (triples : α → Finset (Fin h)) (current : ℕ → Finset α) :
    RankTrace.finish (dualLabels triples (event.after current)) (eventUndo event triples current) =
      dualLabels triples current := by
  have he : dualLabels triples (event.after current) =
      fun i => (Labels.rational h).orthogonal
        (RankTrace.finish (fun j => FanoutFrames.label triples (current j)) (event.updates triples) i) := by
    funext i
    exact congrArg (Labels.rational h).orthogonal (congrFun (event.after_labels triples current) i)
  rw [he]
  exact DAGComplementTrace.undo_finish _ _ _

/-- Exact local complementary inverse identity on arbitrary module contents. -/
theorem event_inverse_run (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) (hl : event.gate.HasLayout) (x : ℕ → E) :
    FramedCircuit.run (eventInverse triples frameOf current event)
      (encode (fun i => frameOf (dualLabels triples (event.after current) i)) x) =
      encode (fun i => frameOf (dualLabels triples current i)) (moduleRun event.gate.program.reverse x) := by
  obtain ⟨layout,hi,ho⟩ := hl
  have hc : ∀ gate ∈ event.gate.program.reverse, ∀ i ∈ FramedCircuit.touched gate,
      frameOf (dualLabels triples (event.after current) i) =
        frameOf ((Labels.rational h).orthogonal (FanoutFrames.label triples event.support)) := by
    intro gate hg i hit
    have hg' : gate ∈ layout.program := by
      rw [← DAGAllocator.Gate.program_eq_layout event.gate layout hi ho]
      exact List.mem_reverse.mp hg
    have hinc := FanoutFrames.touched_subset layout gate hg' i hit
    rw [hi,ho] at hinc
    simp [dualLabels,Event.after,hinc]
  rw [eventInverse,FramedCircuit.run_append,FanoutFrames.run_gate_instructions,
    FanoutFrames.moduleRun_common _ _ _ hc,align_invariant,event_undo_finish]

/-- The chronological reverse event list retains every gate boundary. -/
def schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) :
    List (Event α) → (ℕ → Finset α) → List (Instruction ℕ (ZMod 2) E)
  | [], _ => []
  | event::rest, current => schedule triples frameOf rest (event.after current) ++
      eventInverse triples frameOf current event

/-- Label updates occur after each inverse event, in precisely its reversed
forward incidence order; this definition retains event boundaries. -/
def trace (triples : α → Finset (Fin h)) :
    List (Event α) → (ℕ → Finset α) → List (ℕ × Submodule ℚ (Fin h → ℚ))
  | [], _ => []
  | event::rest, current => trace triples rest (event.after current) ++ eventUndo event triples current

/-- The event-structured physical reverse alignment is exactly the proved
complementary reverse of the complete actual forward label trace. -/
theorem trace_eq_undo (triples : α → Finset (Fin h)) (es : List (Event α)) (current : ℕ → Finset α) :
    trace triples es current = DAGComplementTrace.undo (Labels.rational h).orthogonal
      (fun i => FanoutFrames.label triples (current i)) (updates es triples) := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih =>
    simp only [trace,updates,List.flatMap_cons,DAGComplementTrace.undo_append,ih,eventUndo]
    rw [event.after_labels]

theorem erase_eventInverse (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) :
    DAGFramedExecution.erase (eventInverse triples frameOf current event) = event.gate.program.reverse := by
  rw [eventInverse,DAGFramedExecution.erase_append,erase_align,List.append_nil]
  simp [DAGFramedExecution.erase]

theorem erase_schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α) :
    DAGFramedExecution.erase (schedule triples frameOf es current) =
      (es.flatMap fun event => event.gate.program).reverse := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih =>
    rw [schedule,DAGFramedExecution.erase_append,ih,erase_eventInverse,List.flatMap_cons,List.reverse_append]

/-- Complete complementary inverse execution, before any external sink joins. -/
theorem schedule_invariant (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α)
    (hl : ∀ event ∈ es, event.gate.HasLayout) (x : ℕ → E) :
    FramedCircuit.run (schedule triples frameOf es current)
      (encode (fun i => frameOf (dualLabels triples (DAGSupportTrace.run es current) i)) x) =
      encode (fun i => frameOf (dualLabels triples current i))
        (moduleRun (es.flatMap fun event => event.gate.program).reverse x) := by
  induction es generalizing current x with
  | nil => rfl
  | cons event es ih =>
    rw [schedule,FramedCircuit.run_append]
    change FramedCircuit.run (eventInverse triples frameOf current event)
      (FramedCircuit.run (schedule triples frameOf es (event.after current))
        (encode (fun i => frameOf (dualLabels triples (DAGSupportTrace.run es (event.after current)) i)) x)) = _
    rw [ih _ (fun event he => hl event (by simp [he])),
      event_inverse_run triples frameOf current event (hl event (by simp)),
      List.flatMap_cons,List.reverse_append,GroupedModuleFrames.moduleRun_append]

variable [DecidableEq α]

def inverse (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) : List (Instruction ℕ (ZMod 2) E) :=
  schedule triples frameOf (events nodes outputs) (initialSupports nodes outputs)

theorem inverse_trace (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    trace triples (events nodes outputs) (initialSupports nodes outputs) =
      DAGComplementTrace.reverseTrace nodes outputs triples := trace_eq_undo _ _ _

theorem inverse_erasure (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) :
    DAGFramedExecution.erase (inverse nodes outputs triples frameOf) =
      (DAGAllocator.compile nodes outputs).program.reverse := by
  rw [inverse,erase_schedule,DAGFramedExecution.scalar_erasure]

/-- Actual physical inverse on arbitrary stored contents, decoded in complements
of forward terminal labels and encoded in complements of forward input labels. -/
theorem inverse_identity (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) (stored : ℕ → E) :
    FramedCircuit.run (inverse nodes outputs triples frameOf) stored =
      encode (fun i => frameOf (DAGComplementTrace.reverseOutput nodes outputs triples i))
        (moduleRun (DAGAllocator.compile nodes outputs).program.reverse
          (decode (fun i => frameOf (DAGComplementTrace.reverseInput nodes outputs triples i)) stored)) := by
  have he : dualLabels triples (DAGSupportTrace.run (events nodes outputs) (initialSupports nodes outputs)) =
      DAGComplementTrace.reverseInput nodes outputs triples := by
    funext i
    exact congrArg (Labels.rational h).orthogonal
      (congrFun (DAGSupportTrace.run_labels (events nodes outputs) triples (initialSupports nodes outputs)) i)
  conv_lhs => rw [← encode_decode (fun i => frameOf
    (dualLabels triples (DAGSupportTrace.run (events nodes outputs) (initialSupports nodes outputs)) i)) stored]
  rw [inverse,schedule_invariant triples frameOf _ _ (events_layout nodes outputs hv ho),
    DAGFramedExecution.scalar_erasure,he]
  rfl
end Events
end IntegerMultBounds.Networks.DAGComplementExecution
