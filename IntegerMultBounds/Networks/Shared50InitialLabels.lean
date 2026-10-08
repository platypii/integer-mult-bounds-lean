import IntegerMultBounds.Networks.Shared50Frames
import IntegerMultBounds.Networks.DAGSourceRoles
import IntegerMultBounds.Networks.DAGComplementTrace

/-! Exact initial source lines and empty scratch labels for the actual shared
circuit. Repeated semantic labels retain distinct physical source slots. -/

namespace IntegerMultBounds.Networks.Shared50InitialLabels

open DisjointCircuit DAGAllocator NeighborCounts

variable {α : Type*} [DecidableEq α]

/-- The allocator's certified source label is the singleton support at that
physical source slot, with validity discharging the input support equation. -/
theorem source_support (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (entry : ℕ × ℕ) (he : entry ∈ (compile nodes outputs).sources) :
    DAGSupportTrace.initialSupports nodes outputs entry.2 =
      {DAGSourceRoles.label nodes outputs entry he} := by
  rw [DAGSupportTrace.initialSupports_source nodes outputs entry he]
  have hi := (DAGSourceRoles.source_node nodes outputs entry he).choose
  rw [DAGSupportTrace.nodeSupport_get nodes entry.1 hi]
  have hn := DAGValueTransfer.validFrom_get [] nodes hv entry.1 hi
  simpa only [Node.Valid, DAGSourceRoles.label_kind nodes outputs entry he] using hn

variable {h : ℕ}

omit [DecidableEq α] in
@[simp] theorem label_singleton (triples : α → Finset (Fin h)) (source : α) :
    FanoutFrames.label triples {source} = ℚ ∙ (Labels.indicator (triples source) : Fin h → ℚ) := by
  simp [FanoutFrames.label, SharedPointLabels.indexedSpan, SharedPointLabels.sourceSpan]

omit [DecidableEq α] in
@[simp] theorem label_empty (triples : α → Finset (Fin h)) :
    FanoutFrames.label triples ∅ = ⊥ := by
  simp [FanoutFrames.label, SharedPointLabels.indexedSpan, SharedPointLabels.sourceSpan]

attribute [local irreducible] SharedPointReplay.circuit

/-- The actual input triple at one actual physical source entry. -/
def source (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources) : Triple 50 :=
  DAGSourceRoles.label SharedPointReplay.circuit.nodes SharedPointReplay.outputRefs entry he

/-- No extra input-frame hypothesis is needed: the exact initial label is its
original triple's line in the actual rational form. -/
theorem initial_source (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources) :
    Shared50Frames.initialLabels entry.2 = ℚ ∙ (Labels.indicator (source entry he).val : Fin 50 → ℚ) := by
  change FanoutFrames.label (fun T : Triple 50 => T.val)
    (DAGSupportTrace.initialSupports SharedPointReplay.circuit.nodes SharedPointReplay.outputRefs entry.2) = _
  rw [source_support _ _ SharedPointReplay.valid entry he, label_singleton]
  rfl

/-- Every role not initialized as an actual source starts with the bottom label. -/
theorem initial_other (role : ℕ) (hr : role ∉ SharedPointExecution.code.sources.map Prod.snd) :
    Shared50Frames.initialLabels role = ⊥ := by
  change FanoutFrames.label (fun T : Triple 50 => T.val)
    (DAGSupportTrace.initialSupports SharedPointReplay.circuit.nodes SharedPointReplay.outputRefs role) = _
  rw [DAGSupportTrace.initialSupports_other _ _ role hr, label_empty]

/-- The reversed complementary trace ends exactly at the source line's
orthogonal complement, supplying the physical Y endpoint for an original input. -/
theorem reverse_source (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources) :
    DAGComplementTrace.reverseOutput SharedPointReplay.circuit.nodes SharedPointReplay.outputRefs
      (fun T : Triple 50 => T.val) entry.2 =
      (Labels.rational 50).orthogonal (ℚ ∙ (Labels.indicator (source entry he).val : Fin 50 → ℚ)) := by
  change (Labels.rational 50).orthogonal (Shared50Frames.initialLabels entry.2) = _
  rw [initial_source entry he]

/-- Source initialization, support labels and the scalar input refer to the
same input triple at the same physical slot. -/
theorem source_value (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources)
    (input : Triple 50 → ZMod 2) :
    DAGValueTransfer.sourceInput SharedPointReplay.circuit.nodes input entry.1 = input (source entry he) :=
  DAGSourceRoles.sourceInput_label _ _ entry he input

end IntegerMultBounds.Networks.Shared50InitialLabels
