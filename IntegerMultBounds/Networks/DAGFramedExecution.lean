import IntegerMultBounds.Networks.DAGSupportTrace
import IntegerMultBounds.Networks.GroupedModuleFrames

/-! Physical forward frame execution for the actual allocated DAG event list.
Each event aligns all declared incidences and then executes its unchanged
scalar program. The resulting identity holds on arbitrary stored module
states; inverse-complement schedules, sinks, and motif rank assembly are
separate obligations. -/

namespace IntegerMultBounds.Networks.DAGFramedExecution

open DisjointCircuit DAGSupportTrace FramedCircuit

variable {α E : Type*} {h : ℕ} [AddCommGroup E] [Module (ZMod 2) E]

/-- Turn each actual support span into its chosen physical coordinate frame. -/
def profile (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) (current : ℕ → Finset α) :
    ℕ → Frame (ZMod 2) E := fun i => frameOf (FanoutFrames.label triples (current i))

/-- The exact physical instructions for one event. The declared pivot is
aligned even when its literal gather/scatter instruction list is empty. -/
def eventInstructions (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) : List (Instruction ℕ (ZMod 2) E) :=
  edges (profile triples frameOf current) (fun _ => frameOf (FanoutFrames.label triples event.support))
    (event.gate.inputs ++ event.gate.outputs) ++ event.gate.program.map Instruction.gate

/-- The physical schedule follows the actual support update after each event. -/
def schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) :
    List (Event α) → (ℕ → Finset α) → List (Instruction ℕ (ZMod 2) E)
  | [], _ => []
  | event::rest, current => eventInstructions triples frameOf current event ++
      schedule triples frameOf rest (event.after current)

theorem after_profile (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) :
    afterEdges (profile triples frameOf current) (fun _ => frameOf (FanoutFrames.label triples event.support))
      (event.gate.inputs ++ event.gate.outputs) = profile triples frameOf (event.after current) := by
  funext i
  rw [afterEdges_apply]
  by_cases hi : i ∈ event.gate.inputs ++ event.gate.outputs <;> simp [hi,profile,Event.after]

theorem eventInstructions_eq_framed (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) (layout : ReversibleFanout.Layout ℕ)
    (hi : layout.inputs = event.gate.inputs) (ho : layout.outputs = event.gate.outputs) :
    eventInstructions triples frameOf current event =
      FanoutFrames.framed layout (profile triples frameOf current)
        (frameOf (FanoutFrames.label triples event.support)) := by
  unfold eventInstructions FanoutFrames.framed
  rw [hi,ho,DAGAllocator.Gate.program_eq_layout event.gate layout hi ho]

/-- One actual event has the exact local execution identity, with its real
support-alignment profile and its real scalar gate list. -/
theorem event_run (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) (hl : event.gate.HasLayout) (x : ℕ → E) :
    FramedCircuit.run (eventInstructions triples frameOf current event)
      (encode (profile triples frameOf current) x) =
      encode (profile triples frameOf (event.after current)) (moduleRun event.gate.program x) := by
  obtain ⟨layout,hi,ho⟩ := hl
  rw [eventInstructions_eq_framed triples frameOf current event layout hi ho, FanoutFrames.framed_run,
    hi,ho,after_profile,← DAGAllocator.Gate.program_eq_layout event.gate layout hi ho]

/-- Every intermediate physical frame cancels in the actual event order. -/
theorem schedule_invariant (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α)
    (hl : ∀ event ∈ es, event.gate.HasLayout) (x : ℕ → E) :
    FramedCircuit.run (schedule triples frameOf es current) (encode (profile triples frameOf current) x) =
      encode (profile triples frameOf (DAGSupportTrace.run es current))
        (moduleRun (es.flatMap fun event => event.gate.program) x) := by
  induction es generalizing current x with
  | nil => rfl
  | cons event es ih =>
    rw [schedule,FramedCircuit.run_append,event_run triples frameOf current event (hl event (by simp)),
      ih _ (fun event he => hl event (by simp [he]))]
    simp only [DAGSupportTrace.run,List.flatMap_cons,GroupedModuleFrames.moduleRun_append]

/-- The final physical profile is exactly the accumulated actual rank trace. -/
theorem final_profile (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α) :
    profile triples frameOf (DAGSupportTrace.run es current) =
      fun i => frameOf (RankTrace.finish (fun j => FanoutFrames.label triples (current j))
        (DAGSupportTrace.updates es triples) i) := by
  funext i
  exact congrArg frameOf (congrFun (DAGSupportTrace.run_labels es triples current) i)

/-- Erasing event boundaries gives exactly the compiler's actual scalar
program, retaining every allocated gate, including identity-node events. -/
theorem scalar_erasure (nodes : List (Node α)) (outputs : List ℕ) :
    ((DAGSupportTrace.events nodes outputs).flatMap fun event => event.gate.program) =
      (DAGAllocator.compile nodes outputs).program := by
  rw [DAGAllocator.Code.program,← DAGSupportTrace.events_erasure]
  simp only [List.flatMap_map]

/-- Erase only physical frame changes, retaining each actual scalar instruction. -/
def erase : List (Instruction ℕ (ZMod 2) E) → Circuit.Program ℕ (ZMod 2) :=
  List.filterMap (fun instr => match instr with | .edge _ _ _ => none | .gate gate => some gate)

theorem erase_append (left right : List (Instruction ℕ (ZMod 2) E)) :
    erase (left ++ right) = erase left ++ erase right := List.filterMap_append

theorem erase_edges (current desired : ℕ → Frame (ZMod 2) E) (wires : List ℕ) :
    erase (edges current desired wires) = [] := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih =>
      simpa only [edges,erase,List.filterMap_cons] using ih (Function.update current i (desired i))

theorem erase_event (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (current : ℕ → Finset α) (event : Event α) :
    erase (eventInstructions triples frameOf current event) = event.gate.program := by
  rw [eventInstructions,erase_append,erase_edges,List.nil_append]
  simp [erase]

theorem erase_schedule (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E)
    (es : List (Event α)) (current : ℕ → Finset α) :
    erase (schedule triples frameOf es current) = es.flatMap (fun event => event.gate.program) := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih => rw [schedule,erase_append,erase_event,ih,List.flatMap_cons]

variable [DecidableEq α]

/-- Physical forward execution generated directly from the actual allocator. -/
def forward (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) : List (Instruction ℕ (ZMod 2) E) :=
  schedule triples frameOf (DAGSupportTrace.events nodes outputs) (initialSupports nodes outputs)

/-- No scalar instruction is added or removed by forward frame compilation. -/
theorem forward_erasure (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) :
    erase (forward nodes outputs triples frameOf) = (DAGAllocator.compile nodes outputs).program := by
  rw [forward,erase_schedule,scalar_erasure]

/-- Complete physical forward identity on arbitrary stored contents. Initial
frame decoding is interpretation, and every intermediate frame cancels. The
scalar middle is the actual allocated program, without an execution oracle. -/
theorem forward_identity (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h))
    (frameOf : Submodule ℚ (Fin h → ℚ) → Frame (ZMod 2) E) (stored : ℕ → E) :
    FramedCircuit.run (forward nodes outputs triples frameOf) stored =
      encode (fun i => frameOf (RankTrace.finish
        (fun j => FanoutFrames.label triples (initialSupports nodes outputs j))
        (DAGSupportTrace.updates (DAGSupportTrace.events nodes outputs) triples) i))
        (moduleRun (DAGAllocator.compile nodes outputs).program
          (decode (profile triples frameOf (initialSupports nodes outputs)) stored)) := by
  conv_lhs => rw [← encode_decode (profile triples frameOf (initialSupports nodes outputs)) stored]
  rw [forward,schedule_invariant triples frameOf _ _ (events_layout nodes outputs hv ho),
    scalar_erasure,final_profile]

end IntegerMultBounds.Networks.DAGFramedExecution
