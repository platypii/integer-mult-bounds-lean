import IntegerMultBounds.Networks.Shared50StageFrames
import IntegerMultBounds.Networks.Shared50OutputRoles
import IntegerMultBounds.Networks.Shared50SparseIO
import IntegerMultBounds.Networks.Shared50SparseCentral
import IntegerMultBounds.Networks.LabeledMotif

/-! Concrete frame profiles at the sparse optimized invocation's scalar block
boundaries. Explicit alignments allow early mixers to use the common frame,
actual DAG events to use their source spans, and cleanup to use the full frame.
Only the central return decreases; all source/readout attachment premises are
proved from the actual compiled physical roles. -/

namespace IntegerMultBounds.Networks.Shared50LabeledInvocation

open scoped TensorProduct
open Circuit MotifLabels Shared50StageFrames NeighborCounts

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code

variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup H] [Module ℚ H]

abbrev Wire (n s : ℕ) := Role n 509194 50 s
abbrev Space (E H : Type*) [AddCommGroup E] [Module ℚ E] [AddCommGroup H] [Module ℚ H] :=
  Submodule ℚ ((E ⊗[ℚ] Factor) ⊗[ℚ] H)

/-- The physical data triple represented by this invocation's local index. -/
def indicator (e : Fin n ≃ Triple 50) (i : Fin n) : Factor := Labels.indicator (e i).val

def low (g : Geometry ℚ E Factor) (q : H) : Space E H := Geometry.liftLabel q g.common
def high (g : Geometry ℚ E Factor) (q : H) : Space E H := Geometry.liftLabel q g.full
def xIn (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) (i : Fin n) : Space E H :=
  Geometry.liftLabel q (g.xIn (indicator e i))
def xMid (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) (i : Fin n) : Space E H :=
  Geometry.liftLabel q (g.xMiddle (indicator e i))
def yIn (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) (i : Fin n) : Space E H :=
  Geometry.liftLabel q (g.yIn (indicator e i))
def yOut (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) (i : Fin n) : Space E H :=
  Geometry.liftLabel q (g.yOut (indicator e i))

/-- A physical partial output belongs to a unique data target. -/
theorem partial_target_unique (e : Fin n ≃ Triple 50) (i j : Fin n)
    (c : {c : Fin 50 // c ∈ (e i).val}) (d : {c : Fin 50 // c ∈ (e j).val})
    (h : Shared50Dirty.partialRole (e i) c = Shared50Dirty.partialRole (e j) d) : i = j := by
  exact e.injective ((Shared50OutputRoles.role_eq_iff _ _ c d).mp h).1

/-- A readout role's target is recovered from the real partial-output slots. -/
def IsRead (e : Fin n ≃ Triple 50) (role : Fin 509194) (i : Fin n) : Prop :=
  ∃ c : {c : Fin 50 // c ∈ (e i).val}, Shared50Dirty.partialRole (e i) c = role

noncomputable def readFrame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : Space E H := by
  classical
  exact if h : ∃ i, IsRead e role i then yOut g q e h.choose
    else label g q (Shared50Frames.finalLabels role.val)

theorem readFrame_at (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (i : Fin n) (c : {c : Fin 50 // c ∈ (e i).val}) :
    readFrame g q e (Shared50Dirty.partialRole (e i) c) = yOut g q e i := by
  classical
  have he : ∃ j, IsRead e (Shared50Dirty.partialRole (e i) c) j := ⟨i,c,rfl⟩
  rw [readFrame,dite_eq_left he]
  obtain ⟨d,hd⟩ := he.choose_spec
  exact congrArg (yOut g q e) (partial_target_unique e _ i d c hd)

/-- Actual final partial-output spans attach to their uniquely determined Y. -/
theorem computed_le_readFrame (g : Geometry ℚ E Factor)
    (hcurrent : g.current = Labels.rational 50) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : label g q (Shared50Frames.finalLabels role.val) ≤ readFrame g q e role := by
  classical
  unfold readFrame
  split_ifs with h
  · obtain ⟨c,hc⟩ := h.choose_spec
    have hh := label_mono g q (Shared50OutputRoles.final_orthogonal (e h.choose) c)
    rw [hc] at hh
    simpa only [label,middle_complement_line g hcurrent,yOut,indicator] using hh
  · exact le_rfl

theorem readFrame_le_high (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : readFrame g q e role ≤ high g q := by
  classical
  unfold readFrame
  split_ifs
  · exact Geometry.liftLabel_mono q (g.yOut_le_full _)
  · exact (scratch_attachments g q _).2

/-- Data inputs and physically empty auxiliary/spectator endpoints. -/
def input (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xIn g q e) (yIn g q e) (fun _ => ⊥) (fun _ => ⊥) (fun _ => ⊥)

/-- Reused scratch enters at the proved stage-common frame instead of bottom. -/
def commonInput (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xIn g q e) (yIn g q e) (fun _ => low g q) (fun _ => low g q) (fun _ => ⊥)

/-- The first four scalar blocks L,J,L inverse,R all use this common profile. -/
def early (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xIn g q e) (fun _ => low g q) (fun _ => low g q) (fun _ => low g q) (fun _ => ⊥)

/-- Source loading aligns the exact actual initial labels and matching X lines. -/
def loaded (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xMid g q e) (fun _ => low g q)
    (fun i => label g q (Shared50Frames.initialLabels i.val)) (fun _ => low g q) (fun _ => ⊥)

def gathered (g : Geometry ℚ E Factor) (q : H) : Wire n s → Space E H :=
  banks (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50Frames.initialLabels i.val)) (fun _ => high g q) (fun _ => ⊥)

def returned (g : Geometry ℚ E Factor) (q : H) : Wire n s → Space E H :=
  banks (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50Frames.initialLabels i.val)) (fun _ => low g q) (fun _ => ⊥)

def computed (g : Geometry ℚ E Factor) (q : H) : Wire n s → Space E H :=
  banks (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50Frames.finalLabels i.val)) (fun _ => low g q) (fun _ => ⊥)

noncomputable def readout (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (fun _ => high g q) (yOut g q e) (readFrame g q e) (fun _ => low g q) (fun _ => ⊥)

/-- All cleanup uses the full frame; Y retains its prescribed complement. -/
def output (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (fun _ => high g q) (yOut g q e) (fun _ => high g q) (fun _ => high g q) (fun _ => high g q)

theorem input_le_early (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : input g q e r ≤ early g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact Geometry.liftLabel_mono q (g.yIn_le_common _)
  · exact bot_le
  · exact bot_le
  · exact le_rfl

theorem commonInput_le_early (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : commonInput g q e r ≤ early g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact Geometry.liftLabel_mono q (g.yIn_le_common _)
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem early_le_loaded (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : early g q e r ≤ loaded g q e r := by
  rcases r with i | i | i | i | i
  · exact Geometry.liftLabel_mono q (g.xIn_le_middle _)
  · exact le_rfl
  · exact (scratch_attachments g q _).1
  · exact le_rfl
  · exact le_rfl

theorem loaded_le_gathered (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : loaded g q e r ≤ gathered g q r := by
  rcases r with i | i | i | i | i
  · exact Geometry.liftLabel_mono q (g.middle_le_full _)
  · exact le_rfl
  · exact le_rfl
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact le_rfl

theorem returned_le_gathered (g : Geometry ℚ E Factor) (q : H) (r : Wire n s) :
    returned g q r ≤ gathered g q r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact le_rfl

theorem computed_le_readout (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ Triple 50) (r : Wire n s) : computed g q r ≤ readout g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact Geometry.liftLabel_mono q le_sup_left
  · exact computed_le_readFrame g hcurrent q e i
  · exact le_rfl
  · exact le_rfl

theorem readout_le_output (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : readout g q e r ≤ output g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact le_rfl
  · exact readFrame_le_high g q e i
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact bot_le

/-- Sparse loading puts each actual source and its semantic data input in one frame. -/
theorem loaded_source_frame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (entry : Shared50SparseIO.Source) :
    loaded (s := s) g q e (side (Shared50SparseIO.sourceRole entry)) =
      loaded (s := s) g q e (x (e.symm (Shared50SparseIO.sourceLabel entry))) := by
  change label g q (Shared50Frames.initialLabels entry.val.2) = _
  rw [Shared50InitialLabels.initial_source entry.val entry.property]
  change Geometry.liftLabel q (g.xMiddle (Labels.indicator (Shared50InitialLabels.source entry.val entry.property).val)) =
    Geometry.liftLabel q (g.xMiddle (indicator e (e.symm (Shared50SparseIO.sourceLabel entry))))
  simp only [indicator,Equiv.apply_symm_apply]
  rfl

/-- Sparse readout aligns its actual partial-output source with its Y destination. -/
theorem readout_source_frame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (i : Fin n) (c : {c : Fin 50 // c ∈ (e i).val}) :
    readout (s := s) g q e (side (Shared50Dirty.partialRole (e i) c)) = readout (s := s) g q e (y i) :=
  readFrame_at g q e i c

section Nondegeneracy
variable [FiniteDimensional ℚ E] [FiniteDimensional ℚ H]

omit [FiniteDimensional ℚ E] in
private theorem triple_norm (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (T : Triple 50) : g.current (Labels.indicator T.val) (Labels.indicator T.val) ≠ 0 := by
  rw [hcurrent,Labels.rational_self T.val T.property]
  norm_num

private theorem finish_property {ι L : Type*} [DecidableEq ι]
    (P : L → Prop) (current : ι → L) (xs : List (ι × L))
    (hc : ∀ i, P (current i)) (he : ∀ p ∈ RankTrace.edges current xs, P p.2) :
    ∀ i, P (RankTrace.finish current xs i) := by
  induction xs generalizing current with
  | nil => exact hc
  | cons p xs ih =>
    obtain ⟨j,next⟩ := p
    apply ih (Function.update current j next)
    · intro i
      by_cases h : i = j
      · subst i
        simp only [Function.update_self]
        exact he (current j,next) (by simp [RankTrace.edges])
      · simpa [h] using hc i
    · intro p hp
      exact he p (by simp only [RankTrace.edges,List.mem_cons]; exact Or.inr hp)

omit [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] in
theorem initial_span_nondegenerate (i : ℕ) :
    ((Labels.rational 50).restrict (Shared50Frames.initialLabels i)).Nondegenerate := by
  classical
  by_cases hi : i ∈ SharedPointExecution.code.sources.map Prod.snd
  · obtain ⟨entry,he,hi⟩ := List.mem_map.mp hi
    rw [← hi,Shared50InitialLabels.initial_source entry he]
    apply Labels.line_nondegenerate
    rw [Labels.rational_self _ (Shared50InitialLabels.source entry he).property]
    norm_num
  · rw [Shared50InitialLabels.initial_other i hi]
    exact MotifLabels.bot_nondegenerate _

omit [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] in
theorem final_span_nondegenerate (i : ℕ) :
    ((Labels.rational 50).restrict (Shared50Frames.finalLabels i)).Nondegenerate :=
  finish_property (fun U => ((Labels.rational 50).restrict U).Nondegenerate)
    Shared50Frames.initialLabels Shared50Frames.updates initial_span_nondegenerate
    (fun p hp => (Shared50Frames.nondegenerate p hp).2) i

variable (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50)

include hq

private theorem low_nd : ((g.liftedPairing D).restrict (low g q)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ g.common_nondegenerate
private theorem high_nd : ((g.liftedPairing D).restrict (high g q)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ g.full_nondegenerate
include hcurrent

private theorem yOut_nd (i : Fin n) : ((g.liftedPairing D).restrict (yOut g q e i)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ (g.yOut_nondegenerate _ (triple_norm g hcurrent (e i)))

private theorem readFrame_nd (role : Fin 509194) :
    ((g.liftedPairing D).restrict (readFrame g q e role)).Nondegenerate := by
  classical
  by_cases h : ∃ i, IsRead e role i
  · rw [readFrame,dite_eq_left h]
    exact yOut_nd g hcurrent D q hq e _
  · rw [readFrame,dite_eq_right h]
    exact label_nondegenerate g hcurrent D q hq _ (final_span_nondegenerate _)

theorem input_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (input g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xIn_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact g.liftLabel_nondegenerate D q hq _ (g.yIn_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact MotifLabels.bot_nondegenerate _
  · exact MotifLabels.bot_nondegenerate _
  · exact MotifLabels.bot_nondegenerate _

theorem commonInput_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (commonInput g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xIn_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact g.liftLabel_nondegenerate D q hq _ (g.yIn_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact low_nd g D q hq
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem early_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (early g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xIn_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact low_nd g D q hq
  · exact low_nd g D q hq
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem loaded_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (loaded g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xMiddle_nondegenerate _ (triple_norm g hcurrent (e i)))
  · exact low_nd g D q hq
  · exact label_nondegenerate g hcurrent D q hq _ (initial_span_nondegenerate _)
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem gathered_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (gathered g q r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact low_nd g D q hq
  · exact label_nondegenerate g hcurrent D q hq _ (initial_span_nondegenerate _)
  · exact high_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem returned_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (returned g q r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact low_nd g D q hq
  · exact label_nondegenerate g hcurrent D q hq _ (initial_span_nondegenerate _)
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem computed_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (computed g q r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact low_nd g D q hq
  · exact label_nondegenerate g hcurrent D q hq _ (final_span_nondegenerate _)
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem readout_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (readout g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact yOut_nd g hcurrent D q hq e i
  · exact readFrame_nd g hcurrent D q hq e i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem output_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (output g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact yOut_nd g hcurrent D q hq e i
  · exact high_nd g D q hq
  · exact high_nd g D q hq
  · exact high_nd g D q hq

end Nondegeneracy

end IntegerMultBounds.Networks.Shared50LabeledInvocation
