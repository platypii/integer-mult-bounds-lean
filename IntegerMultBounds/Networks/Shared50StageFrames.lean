import IntegerMultBounds.Networks.Shared50ComplementFrames
import IntegerMultBounds.Networks.Shared50InitialLabels
import IntegerMultBounds.Networks.MotifLabels
import IntegerMultBounds.Networks.StageLabels

/-! Actual fifty-copy middle-computation frames in a stage geometry.
D_U is the orthogonal sum of B tensor F and P tensor U, followed by the actual
future line Q. Forward and reversed-complement traces remain increasing and
nondegenerate with zero loss. Whole-motif central returns and global rank
assembly are not included here. -/

namespace IntegerMultBounds.Networks.Shared50StageFrames

open scoped TensorProduct
open MotifLabels TensorSubspace NeighborCounts SharedPointReplay

attribute [local irreducible] SharedPointReplay.circuit

section TraceTransport
variable {L M : Type*}

def mapUpdates (f : L → M) (xs : List (ℕ × L)) : List (ℕ × M) :=
  xs.map fun p => (p.1,f p.2)

theorem finish_map (f : L → M) (current : ℕ → L) (xs : List (ℕ × L)) :
    RankTrace.finish (fun i => f (current i)) (mapUpdates f xs) =
      fun i => f (RankTrace.finish current xs i) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,next⟩ := p
    have he : Function.update (fun j => f (current j)) i (f next) =
        fun j => f (Function.update current i next j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    simpa only [mapUpdates,List.map_cons,RankTrace.finish,he] using ih (Function.update current i next)

theorem edges_map (f : L → M) (current : ℕ → L) (xs : List (ℕ × L)) :
    RankTrace.edges (fun i => f (current i)) (mapUpdates f xs) =
      (RankTrace.edges current xs).map (fun p => (f p.1,f p.2)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,next⟩ := p
    have he : Function.update (fun j => f (current j)) i (f next) =
        fun j => f (Function.update current i next j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    simp only [mapUpdates,List.map_cons,RankTrace.edges,he]
    exact congrArg (List.cons (f (current i),f next)) (ih (Function.update current i next))
end TraceTransport

abbrev Factor := Fin 50 → ℚ

section Geometry
variable {E H : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup H] [Module ℚ H]

/-- The actual middle stage space D_U, before tensoring by the future line. -/
def middle (g : Geometry ℚ E Factor) (U : Submodule ℚ Factor) : Submodule ℚ (E ⊗[ℚ] Factor) :=
  g.common ⊔ space g.past U

/-- Restore the actual one-dimensional future factor Q. -/
def label (g : Geometry ℚ E Factor) (q : H) (U : Submodule ℚ Factor) :
    Submodule ℚ ((E ⊗[ℚ] Factor) ⊗[ℚ] H) := Geometry.liftLabel q (middle g U)

theorem middle_mono (g : Geometry ℚ E Factor) {U V : Submodule ℚ Factor} (hUV : U ≤ V) :
    middle g U ≤ middle g V := sup_le_sup le_rfl (TensorSubspace.mono le_rfl hUV)

theorem label_mono (g : Geometry ℚ E Factor) (q : H) {U V : Submodule ℚ Factor} (hUV : U ≤ V) :
    label g q U ≤ label g q V := Geometry.liftLabel_mono q (middle_mono g hUV)

theorem middle_nondegenerate [FiniteDimensional ℚ E] (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (U : Submodule ℚ Factor) (hU : ((Labels.rational 50).restrict U).Nondegenerate) :
    (g.pairing.restrict (middle g U)).Nondegenerate := by
  apply orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
  · apply TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate
    simpa only [hcurrent] using hU
  · exact g.common_orthogonal_past U

theorem label_nondegenerate [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0)
    (U : Submodule ℚ Factor) (hU : ((Labels.rational 50).restrict U).Nondegenerate) :
    ((g.liftedPairing D).restrict (label g q U)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ (middle_nondegenerate g hcurrent U hU)

theorem middle_bot (g : Geometry ℚ E Factor) : middle g ⊥ = g.common := by
  have hz : space g.past (⊥ : Submodule ℚ Factor) = ⊥ := by
    apply le_antisymm _ bot_le
    apply StageLabels.space_le
    intro x hx y hy
    have hy' : y = 0 := by simpa using hy
    simp [hy']
  rw [middle,hz,sup_bot_eq]

theorem middle_top (g : Geometry ℚ E Factor) : middle g ⊤ = g.full := by
  change space g.base ⊤ ⊔ space g.past ⊤ = space ⊤ ⊤
  rw [← TensorSubspace.sup_left,g.base_sup_past]

theorem middle_line (g : Geometry ℚ E Factor) (t : Factor) : middle g (ℚ ∙ t) = g.xMiddle t := rfl

theorem middle_complement_line (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (t : Factor) : middle g ((Labels.rational 50).orthogonal (ℚ ∙ t)) = g.yOut t := by
  simp only [middle,Geometry.yOut,hcurrent]

/-- Physical source X lines attach increasingly to their middle computation. -/
theorem source_attachment (g : Geometry ℚ E Factor) (q : H) (t : Factor) :
    Geometry.liftLabel q (g.xIn t) ≤ label g q (ℚ ∙ t) :=
  Geometry.liftLabel_mono q (g.xIn_le_middle t)

/-- Empty scratch enters at D_0 and retired scratch can leave at D_1. -/
theorem scratch_attachments (g : Geometry ℚ E Factor) (q : H) (U : Submodule ℚ Factor) :
    Geometry.liftLabel q g.common ≤ label g q U ∧ label g q U ≤ Geometry.liftLabel q g.full := by
  constructor
  · exact Geometry.liftLabel_mono q le_sup_left
  · apply Geometry.liftLabel_mono q
    rw [g.full_eq_top]
    exact le_top

/-- Actual forward output labels attach to the prescribed Y complement. -/
theorem forward_output_attachment (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (c : Fin 50) (j : Fin 1176) :
    label g q (Shared50Frames.finalLabels (SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j))) ≤
      Geometry.liftLabel q (g.yOut (Labels.indicator (embedding c j).val)) := by
  have hh := label_mono g q (Shared50Frames.final_orthogonal c j)
  simpa only [label,middle_complement_line g hcurrent] using hh

/-- Reverse middle computation begins above the physical target X line. -/
theorem reverse_input_attachment (g : Geometry ℚ E Factor) (q : H) (c : Fin 50) (j : Fin 1176) :
    Geometry.liftLabel q (g.xIn (Labels.indicator (embedding c j).val)) ≤
      label g q (Shared50ComplementFrames.input
        (SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j))) :=
  (source_attachment g q _).trans (label_mono g q (Shared50ComplementFrames.target_le_input c j))

/-- Complemented source lines end exactly at the physical Y complement. -/
theorem reverse_source_attachment (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (t : Factor) :
    label g q ((Labels.rational 50).orthogonal (ℚ ∙ t)) = Geometry.liftLabel q (g.yOut t) := by
  rw [label,middle_complement_line g hcurrent]

/-- The concrete source-slot support, not a hypothetical line, supplies X. -/
theorem initial_source_attachment (g : Geometry ℚ E Factor) (q : H)
    (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources) :
    Geometry.liftLabel q (g.xIn (Labels.indicator (Shared50InitialLabels.source entry he).val)) ≤
      label g q (Shared50Frames.initialLabels entry.2) := by
  rw [Shared50InitialLabels.initial_source entry he]
  exact source_attachment g q _

/-- At a concrete original source slot the reverse terminal frame is Y. -/
theorem terminal_source_attachment (g : Geometry ℚ E Factor)
    (hcurrent : g.current = Labels.rational 50) (q : H)
    (entry : ℕ × ℕ) (he : entry ∈ SharedPointExecution.code.sources) :
    label g q (Shared50ComplementFrames.output entry.2) =
      Geometry.liftLabel q (g.yOut (Labels.indicator (Shared50InitialLabels.source entry he).val)) := by
  rw [Shared50ComplementFrames.output_eq,Shared50InitialLabels.initial_source entry he]
  exact reverse_source_attachment g hcurrent q _

/-- Every nonsource role has precisely the common initial scratch frame. -/
theorem initial_scratch (g : Geometry ℚ E Factor) (q : H) (role : ℕ)
    (hr : role ∉ SharedPointExecution.code.sources.map Prod.snd) :
    label g q (Shared50Frames.initialLabels role) = Geometry.liftLabel q g.common := by
  rw [Shared50InitialLabels.initial_other role hr,label,middle_bot]

/-- Every nonsource role has precisely the full reverse terminal scratch frame. -/
theorem terminal_scratch (g : Geometry ℚ E Factor) (q : H) (role : ℕ)
    (hr : role ∉ SharedPointExecution.code.sources.map Prod.snd) :
    label g q (Shared50ComplementFrames.output role) = Geometry.liftLabel q g.full := by
  rw [Shared50ComplementFrames.output_eq,Shared50InitialLabels.initial_other role hr]
  simp only [LinearMap.BilinForm.orthogonal_bot,label,middle_top]

/-- Common-point provenance applies to every actual compiled event. -/
theorem event_span_nondegenerate (event : DAGSupportTrace.Event (Triple 50))
    (he : event ∈ Shared50Frames.events) :
    ((Labels.rational 50).restrict (FanoutFrames.label Shared50ComplementFrames.triples event.support)).Nondegenerate := by
  obtain ⟨node,hn,hs⟩ := DAGSupportTrace.events_support circuit.nodes outputRefs event he
  obtain ⟨common,hcommon⟩ := Shared50Frames.node_common node hn
  rw [hs]
  exact SharedPointLabels.indexedSpan_nondegenerate common _ _
    (fun T hT => (hcommon T hT).1) (fun T hT => (hcommon T hT).2)

/-- The literal forward event frame D_U tensor Q is nondegenerate. -/
theorem forward_event_nondegenerate [FiniteDimensional ℚ E] [FiniteDimensional ℚ H]
    (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0)
    (event : DAGSupportTrace.Event (Triple 50)) (he : event ∈ Shared50Frames.events) :
    ((g.liftedPairing D).restrict
      (label g q (FanoutFrames.label Shared50ComplementFrames.triples event.support))).Nondegenerate :=
  label_nondegenerate g hcurrent D q hq _ (event_span_nondegenerate event he)

/-- Reverse events complement U before constructing D_U and restoring Q. -/
theorem reverse_event_nondegenerate [FiniteDimensional ℚ E] [FiniteDimensional ℚ H]
    (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0)
    (event : DAGSupportTrace.Event (Triple 50)) (he : event ∈ Shared50Frames.events) :
    ((g.liftedPairing D).restrict (label g q ((Labels.rational 50).orthogonal
      (FanoutFrames.label Shared50ComplementFrames.triples event.support)))).Nondegenerate :=
  label_nondegenerate g hcurrent D q hq _
    (ProjectionRank.orthogonal_nondegenerate _ ⟨Labels.form_symm (1 / 9)⟩
      (Labels.rational_nondegenerate (by decide)) _ (event_span_nondegenerate event he))

/-- Actual forward/reversed traces with no changes to the incidence lists. -/
def forwardUpdates (g : Geometry ℚ E Factor) (q : H) := mapUpdates (label g q) Shared50Frames.updates

def reverseUpdates (g : Geometry ℚ E Factor) (q : H) := mapUpdates (label g q) Shared50ComplementFrames.updates

/-- Forward endpoints are the actual compiled terminal profile transported by D and Q. -/
theorem forward_endpoints (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.finish (fun i => label g q (Shared50Frames.initialLabels i)) (forwardUpdates g q) =
      fun i => label g q (Shared50Frames.finalLabels i) := finish_map _ _ _

/-- Reversal restores the complemented actual initial profile at every role. -/
theorem reverse_endpoints (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.finish (fun i => label g q (Shared50ComplementFrames.input i)) (reverseUpdates g q) =
      fun i => label g q (Shared50ComplementFrames.output i) := by
  rw [reverseUpdates,finish_map,Shared50ComplementFrames.endpoints]

theorem forward_edges (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.edges (fun i => label g q (Shared50Frames.initialLabels i)) (forwardUpdates g q) =
      (RankTrace.edges Shared50Frames.initialLabels Shared50Frames.updates).map
        (fun p => (label g q p.1,label g q p.2)) := edges_map _ _ _

theorem reverse_edges (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.edges (fun i => label g q (Shared50ComplementFrames.input i)) (reverseUpdates g q) =
      (RankTrace.edges Shared50ComplementFrames.input Shared50ComplementFrames.updates).map
        (fun p => (label g q p.1,label g q p.2)) := edges_map _ _ _

theorem forward_increasing (g : Geometry ℚ E Factor) (q : H) :
    ∀ p ∈ RankTrace.edges (fun i => label g q (Shared50Frames.initialLabels i)) (forwardUpdates g q), p.1 ≤ p.2 := by
  intro p hp
  rw [forward_edges] at hp
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  exact label_mono g q (Shared50Frames.increasing old hold)

theorem reverse_increasing (g : Geometry ℚ E Factor) (q : H) :
    ∀ p ∈ RankTrace.edges (fun i => label g q (Shared50ComplementFrames.input i)) (reverseUpdates g q), p.1 ≤ p.2 := by
  intro p hp
  rw [reverse_edges] at hp
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  exact label_mono g q (Shared50ComplementFrames.increasing old hold)

theorem forward_nondegenerate [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) :
    ∀ p ∈ RankTrace.edges (fun i => label g q (Shared50Frames.initialLabels i)) (forwardUpdates g q),
      ((g.liftedPairing D).restrict p.1).Nondegenerate ∧ ((g.liftedPairing D).restrict p.2).Nondegenerate := by
  intro p hp
  rw [forward_edges] at hp
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  have hn := Shared50Frames.nondegenerate old hold
  exact ⟨label_nondegenerate g hcurrent D q hq _ hn.1,label_nondegenerate g hcurrent D q hq _ hn.2⟩

theorem reverse_nondegenerate [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) :
    ∀ p ∈ RankTrace.edges (fun i => label g q (Shared50ComplementFrames.input i)) (reverseUpdates g q),
      ((g.liftedPairing D).restrict p.1).Nondegenerate ∧ ((g.liftedPairing D).restrict p.2).Nondegenerate := by
  intro p hp
  rw [reverse_edges] at hp
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  have hn := Shared50ComplementFrames.nondegenerate old hold
  exact ⟨label_nondegenerate g hcurrent D q hq _ hn.1,label_nondegenerate g hcurrent D q hq _ hn.2⟩

theorem forward_loss_zero [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.loss (fun U : Submodule ℚ ((E ⊗[ℚ] Factor) ⊗[ℚ] H) => Module.finrank ℚ U)
      (fun i => label g q (Shared50Frames.initialLabels i)) (forwardUpdates g q) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (forward_increasing g q p hp))

theorem reverse_loss_zero [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.loss (fun U : Submodule ℚ ((E ⊗[ℚ] Factor) ⊗[ℚ] H) => Module.finrank ℚ U)
      (fun i => label g q (Shared50ComplementFrames.input i)) (reverseUpdates g q) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (reverse_increasing g q p hp))

end Geometry
end IntegerMultBounds.Networks.Shared50StageFrames
