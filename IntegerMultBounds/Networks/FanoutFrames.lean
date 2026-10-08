import IntegerMultBounds.Networks.ReversibleFanout
import IntegerMultBounds.Networks.FramedCircuit
import IntegerMultBounds.Networks.SharedPointLabels
import IntegerMultBounds.Networks.RankTrace

/-! Common-frame execution and increasing source-span labels for one actual
reversible fanout layout. Alignment includes the declared pivot even for an
identity node. Global allocator support propagation is a separate obligation. -/

namespace IntegerMultBounds.Networks.FanoutFrames

open ReversibleFanout FramedCircuit

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every actual scalar incidence lies in the layout's declared input/output
incidence; the declared identity pivot may have no scalar incidence. -/
theorem touched_subset (layout : Layout ι) (gate : Circuit.Gate ι (ZMod 2))
    (hg : gate ∈ layout.program) (i : ι) (hi : i ∈ FramedCircuit.touched gate) :
    i ∈ layout.inputs ++ layout.outputs := by
  simp only [Layout.program, gather, scatter, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨src, hs, rfl⟩ | ⟨dst, hd, rfl⟩
  · have hh : i = layout.pivot ∨ i = src := by simpa [FramedCircuit.touched, add] using hi
    rcases hh with rfl | rfl <;> simp [Layout.inputs, Layout.outputs, hs]
  · have hh : i = dst ∨ i = layout.pivot := by simpa [FramedCircuit.touched, add] using hi
    rcases hh with rfl | rfl <;> simp [Layout.inputs, Layout.outputs, hd]

section Execution
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- A finite list of gate instructions executes precisely its module program. -/
theorem run_gate_instructions (program : Circuit.Program ι R) (x : ι → E) :
    FramedCircuit.run (program.map FramedCircuit.Instruction.gate) x = moduleRun program x := by
  induction program generalizing x with
  | nil => rfl
  | cons gate program ih => simpa only [List.map_cons, FramedCircuit.run_cons,
      FramedCircuit.execute, moduleRun_cons] using ih (moduleGate gate x)

/-- One unchanged frame profile commutes with a program whenever every actual
instruction's incidences share the same frame in that profile. -/
theorem moduleRun_common (program : Circuit.Program ι R) (frames : ι → Frame R E)
    (common : Frame R E) (hc : ∀ gate ∈ program, ∀ i ∈ FramedCircuit.touched gate, frames i = common)
    (x : ι → E) : moduleRun program (encode frames x) = encode frames (moduleRun program x) := by
  induction program generalizing x with
  | nil => rfl
  | cons gate program ih =>
    rw [moduleRun_cons, gate_invariant gate frames common (hc gate (by simp)),
      ih (fun gate hg => hc gate (by simp [hg]))]
    rfl
end Execution

section FanoutExecution
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- First align every declared layout incidence to one common frame, then
execute the literal scalar gather/scatter instruction list unchanged. -/
def framed (layout : Layout ι) (current : ι → Frame (ZMod 2) E) (common : Frame (ZMod 2) E) :
    List (Instruction ι (ZMod 2) E) :=
  edges current (fun _ => common) (layout.inputs ++ layout.outputs) ++
    layout.program.map Instruction.gate

/-- Exact common-frame identity for one literal layout, including identity
layouts, nonpivot inputs, dirty scalar outputs, and untouched spectators. -/
theorem framed_run (layout : Layout ι) (current : ι → Frame (ZMod 2) E)
    (common : Frame (ZMod 2) E) (x : ι → E) :
    FramedCircuit.run (framed layout current common) (encode current x) =
      encode (afterEdges current (fun _ => common) (layout.inputs ++ layout.outputs))
        (moduleRun layout.program x) := by
  rw [framed, FramedCircuit.run_append, edges_invariant, run_gate_instructions]
  apply moduleRun_common _ _ common
  intro gate hg i hi
  simp [afterEdges_apply, touched_subset layout gate hg i hi]
/-- The profile left by the physical alignment is exactly the image of the
explicit label trace, so its rank-accounting labels describe executed edges. -/
theorem afterEdges_profile {L : Type*} (frameOf : L → Frame (ZMod 2) E)
    (current : ι → L) (common : L) (wires : List ι) :
    afterEdges (fun i => frameOf (current i)) (fun _ => frameOf common) wires =
      fun i => frameOf (RankTrace.finish current (wires.map fun i => (i,common)) i) := by
  funext i
  rw [afterEdges_apply, RankTrace.finish_align]
  split_ifs <;> rfl

/-- The exact framed layout execution with the final profile expressed using
its concrete, declared-incidence label update trace. -/
theorem framed_run_labels {L : Type*} (layout : Layout ι) (frameOf : L → Frame (ZMod 2) E)
    (current : ι → L) (common : L) (x : ι → E) :
    FramedCircuit.run (framed layout (fun i => frameOf (current i)) (frameOf common))
      (encode (fun i => frameOf (current i)) x) =
      encode (fun i => frameOf (RankTrace.finish current
        ((layout.inputs ++ layout.outputs).map fun i => (i,common)) i))
        (moduleRun layout.program x) := by
  rw [framed_run, afterEdges_profile]

end FanoutExecution

section Trace
variable {L : Type*} [Preorder L]

/-- Repeated incidences produce identity edges after their first alignment.
Every actual edge ends at the common label and starts below it. -/
theorem align_edges (current : ι → L) (common : L) (wires : List ι)
    (hc : ∀ i ∈ wires, current i ≤ common) :
    ∀ p ∈ RankTrace.edges current (wires.map fun i => (i, common)), p.1 ≤ common ∧ p.2 = common := by
  induction wires generalizing current with
  | nil => simp [RankTrace.edges]
  | cons i wires ih =>
    intro p hp
    simp only [List.map_cons, RankTrace.edges, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hc i (by simp), rfl⟩
    · apply ih (Function.update current i common) _ p hp
      intro j hj
      by_cases he : j = i
      · subst j; simp
      · simpa [he] using hc j (by simp [hj])
end Trace

section SourceLabels
variable {α : Type*} {h : ℕ}

/-- The label is the actual span of supported triple indicators. -/
def label (triples : α → Finset (Fin h)) (support : Finset α) : Submodule ℚ (Fin h → ℚ) :=
  SharedPointLabels.indexedSpan triples (support : Set α)

/-- One declared incidence alignment gives the precise rank-accounting trace
of the concrete framed layout above, including duplicate pivot incidences. -/
def updates (layout : Layout ι) (triples : α → Finset (Fin h)) (support : Finset α) :
    List (ι × Submodule ℚ (Fin h → ℚ)) :=
  (layout.inputs ++ layout.outputs).map fun i => (i, label triples support)

/-- Every declared input/output role ends at the node label, including the
pivot of an identity node with no scalar instructions. -/
theorem finish_incidence (layout : Layout ι) (triples : α → Finset (Fin h))
    (current : ι → Submodule ℚ (Fin h → ℚ)) (support : Finset α) (i : ι)
    (hi : i ∈ layout.inputs ++ layout.outputs) :
    RankTrace.finish current (updates layout triples support) i = label triples support := by
  rw [updates, RankTrace.finish_align]
  simp [hi]

/-- Labels on all nonincident physical roles are preserved exactly. -/
theorem finish_outside (layout : Layout ι) (triples : α → Finset (Fin h))
    (current : ι → Submodule ℚ (Fin h → ℚ)) (support : Finset α) (i : ι)
    (hi : i ∉ layout.inputs ++ layout.outputs) :
    RankTrace.finish current (updates layout triples support) i = current i := by
  rw [updates, RankTrace.finish_align]
  simp [hi]

theorem label_mono (triples : α → Finset (Fin h)) {support larger : Finset α} (hs : support ⊆ larger) :
    label triples support ≤ label triples larger :=
  SharedPointLabels.indexedSpan_mono triples hs

omit [DecidableEq ι] in
/-- Every input has support inside the node support; new output roles start
with empty support. These concrete premises suffice for all declared roles. -/
theorem incidence_subset (layout : Layout ι) (supportAt : ι → Finset α) (support : Finset α)
    (hin : ∀ i ∈ layout.inputs, supportAt i ⊆ support)
    (hfresh : ∀ i ∈ layout.outputTail, supportAt i = ∅) :
    ∀ i ∈ layout.inputs ++ layout.outputs, supportAt i ⊆ support := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hin i hi
  · rcases List.mem_cons.mp hi with rfl | hi
    · exact hin layout.pivot (by simp [Layout.inputs])
    · rw [hfresh i hi]
      exact Finset.empty_subset _

/-- The actual local trace is increasing: labels are derived from supports,
with no externally supplied subspace-comparability premise. -/
theorem edges_increasing (layout : Layout ι) (triples : α → Finset (Fin h))
    (supportAt : ι → Finset α) (support : Finset α)
    (hin : ∀ i ∈ layout.inputs, supportAt i ⊆ support)
    (hfresh : ∀ i ∈ layout.outputTail, supportAt i = ∅) :
    ∀ p ∈ RankTrace.edges (fun i => label triples (supportAt i)) (updates layout triples support),
      p.1 ≤ p.2 := by
  intro p hp
  obtain ⟨hle, he⟩ := align_edges (fun i => label triples (supportAt i)) (label triples support)
    (layout.inputs ++ layout.outputs)
    (fun i hi => label_mono triples (incidence_subset layout supportAt support hin hfresh i hi)) p hp
  rwa [he]

/-- This actual local source-span trace has no dimension-decreasing edges. -/
theorem loss_zero (layout : Layout ι) (triples : α → Finset (Fin h))
    (supportAt : ι → Finset α) (support : Finset α)
    (hin : ∀ i ∈ layout.inputs, supportAt i ⊆ support)
    (hfresh : ∀ i ∈ layout.outputTail, supportAt i = ∅) :
    RankTrace.loss (fun U : Submodule ℚ (Fin h → ℚ) => Module.finrank ℚ U)
      (fun i => label triples (supportAt i)) (updates layout triples support) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (edges_increasing layout triples supportAt support hin hfresh p hp))

/-- Common-point source triples discharge rational nondegeneracy for both
endpoints of every actual local frame edge, including empty source spans. -/
theorem edges_nondegenerate (layout : Layout ι) (triples : α → Finset (Fin h))
    (supportAt : ι → Finset α) (support : Finset α) (common : Fin h)
    (hin : ∀ i ∈ layout.inputs, supportAt i ⊆ support)
    (hfresh : ∀ i ∈ layout.outputTail, supportAt i = ∅)
    (htriples : ∀ a ∈ support, (triples a).card = 3)
    (hcommon : ∀ a ∈ support, common ∈ triples a) :
    ∀ p ∈ RankTrace.edges (fun i => label triples (supportAt i)) (updates layout triples support),
      ((Labels.rational h).restrict p.1).Nondegenerate ∧
      ((Labels.rational h).restrict p.2).Nondegenerate := by
  have hplane : label triples support ≤ SharedPointLabels.sharedPlane common := by
    apply SharedPointLabels.sourceSpan_le_sharedPlane common
    · rintro S ⟨a, ha, rfl⟩; exact htriples a ha
    · rintro S ⟨a, ha, rfl⟩; exact hcommon a ha
  intro p hp
  obtain ⟨hle, he⟩ := align_edges (fun i => label triples (supportAt i)) (label triples support)
    (layout.inputs ++ layout.outputs)
    (fun i hi => label_mono triples (incidence_subset layout supportAt support hin hfresh i hi)) p hp
  exact ⟨SharedPointLabels.subspace_nondegenerate common p.1 (hle.trans hplane),
    SharedPointLabels.subspace_nondegenerate common p.2 (he ▸ hplane)⟩

/-- Projection differences on these executed local frame edges have their
true operator rank equal to the increasing label dimension difference. -/
theorem edge_projection_rank (layout : Layout ι) (triples : α → Finset (Fin h))
    (supportAt : ι → Finset α) (support : Finset α) (common : Fin h)
    (hin : ∀ i ∈ layout.inputs, supportAt i ⊆ support)
    (hfresh : ∀ i ∈ layout.outputTail, supportAt i = ∅)
    (htriples : ∀ a ∈ support, (triples a).card = 3)
    (hcommon : ∀ a ∈ support, common ∈ triples a)
    (p : Submodule ℚ (Fin h → ℚ) × Submodule ℚ (Fin h → ℚ))
    (hp : p ∈ RankTrace.edges (fun i => label triples (supportAt i)) (updates layout triples support)) :
    let hn := edges_nondegenerate layout triples supportAt support common hin hfresh htriples hcommon p hp
    let hs : (Labels.rational h).IsSymm := ⟨Labels.form_symm (1 / 9)⟩
    Module.finrank ℚ (LinearMap.range
      (ProjectionRank.project (Labels.rational h) hs p.2 hn.2 -
        ProjectionRank.project (Labels.rational h) hs p.1 hn.1)) =
      Module.finrank ℚ p.2 - Module.finrank ℚ p.1 := by
  intro hn hs
  exact ProjectionRank.difference_rank (Labels.rational h) hs p.1 p.2 hn.1 hn.2
    (edges_increasing layout triples supportAt support hin hfresh p hp)

end SourceLabels
end IntegerMultBounds.Networks.FanoutFrames
