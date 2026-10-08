import IntegerMultBounds.Networks.Shared50LabeledInvocation
import IntegerMultBounds.Networks.Shared50FiniteReverseTrace

/-! Actual boundary profiles for the opposite, reversed twelve-block invocation.
Output slots first share their physical X target's middle line, then enter the
complemented reverse DAG; original source slots end at their physical Y frames. -/

namespace IntegerMultBounds.Networks.Shared50OppositeLabels

open scoped TensorProduct
open Circuit MotifLabels Shared50StageFrames Shared50LabeledInvocation NeighborCounts

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code

variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup H] [Module ℚ H]

noncomputable def injectFrame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : Space E H := by
  classical
  exact if h : ∃ i, IsRead e role i then xMid g q e h.choose else low g q

theorem injectFrame_at (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (i : Fin n) (c : {c : Fin 50 // c ∈ (e i).val}) :
    injectFrame g q e (Shared50Dirty.partialRole (e i) c) = xMid g q e i := by
  classical
  have he : ∃ j, IsRead e (Shared50Dirty.partialRole (e i) c) j := ⟨i,c,rfl⟩
  rw [injectFrame,dite_eq_left he]
  obtain ⟨d,hd⟩ := he.choose_spec
  exact congrArg (xMid g q e) (partial_target_unique e _ i d c hd)

theorem low_le_injectFrame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : low g q ≤ injectFrame g q e role := by
  classical
  unfold injectFrame
  split_ifs
  · exact Geometry.liftLabel_mono q le_sup_left
  · exact le_rfl

theorem injectFrame_le_reverse (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (role : Fin 509194) : injectFrame g q e role ≤ label g q (Shared50ComplementFrames.input role.val) := by
  classical
  unfold injectFrame
  split_ifs with h
  · obtain ⟨c,hc⟩ := h.choose_spec
    have hh := label_mono g q (Shared50ComplementFrames.target_le_input c.val
      (Shared50Dirty.pairIndex c.val (e h.choose) c.property))
    rw [← Shared50OutputRoles.role_val,Shared50Dirty.pairIndex_spec,hc] at hh
    exact hh
  · exact (scratch_attachments g q _).1

noncomputable def injected (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xMid g q e) (fun _ => low g q) (injectFrame g q e) (fun _ => low g q) (fun _ => ⊥)

def reverseLoaded (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xMid g q e) (fun _ => low g q)
    (fun i => label g q (Shared50ComplementFrames.input i.val)) (fun _ => low g q) (fun _ => ⊥)

def reverseComputed (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (xMid g q e) (fun _ => low g q)
    (fun i => label g q (Shared50ComplementFrames.output i.val)) (fun _ => low g q) (fun _ => ⊥)

def reverseGathered (g : Geometry ℚ E Factor) (q : H) : Wire n s → Space E H :=
  banks (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50ComplementFrames.output i.val)) (fun _ => high g q) (fun _ => ⊥)

def reverseReturned (g : Geometry ℚ E Factor) (q : H) : Wire n s → Space E H :=
  banks (fun _ => high g q) (fun _ => low g q)
    (fun i => label g q (Shared50ComplementFrames.output i.val)) (fun _ => low g q) (fun _ => ⊥)

def drained (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) : Wire n s → Space E H :=
  banks (fun _ => high g q) (yOut g q e)
    (fun i => label g q (Shared50ComplementFrames.output i.val)) (fun _ => low g q) (fun _ => ⊥)

theorem early_le_injected (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : early g q e r ≤ injected g q e r := by
  rcases r with i | i | i | i | i
  · exact Geometry.liftLabel_mono q (g.xIn_le_middle _)
  · exact le_rfl
  · exact low_le_injectFrame g q e i
  · exact le_rfl
  · exact le_rfl

theorem injected_le_reverseLoaded (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : injected g q e r ≤ reverseLoaded g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact le_rfl
  · exact injectFrame_le_reverse g q e i
  · exact le_rfl
  · exact le_rfl

theorem reverseComputed_le_gathered (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : reverseComputed g q e r ≤ reverseGathered g q r := by
  rcases r with i | i | i | i | i
  · exact Geometry.liftLabel_mono q (g.middle_le_full _)
  · exact le_rfl
  · exact le_rfl
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact le_rfl

theorem reverseReturned_le_gathered (g : Geometry ℚ E Factor) (q : H) (r : Wire n s) :
    reverseReturned g q r ≤ reverseGathered g q r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact le_rfl

theorem reverseReturned_le_drained (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : reverseReturned g q r ≤ drained g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact Geometry.liftLabel_mono q le_sup_left
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem drained_le_output (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (r : Wire n s) : drained g q e r ≤ output g q e r := by
  rcases r with i | i | i | i | i
  · exact le_rfl
  · exact le_rfl
  · exact (scratch_attachments g q _).2
  · exact Geometry.liftLabel_mono q g.common_le_full
  · exact bot_le

/-- The opposite readout block's actual source and target share X's frame. -/
theorem injected_source_frame (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (i : Fin n) (c : {c : Fin 50 // c ∈ (e i).val}) :
    injected (s := s) g q e (side (Shared50Dirty.partialRole (e i) c)) =
      injected (s := s) g q e (x i) := injectFrame_at g q e i c

/-- Exact reverse endpoints make opposite source cleanup share Y's frame. -/
theorem drained_source_frame (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ Triple 50) (entry : Shared50SparseIO.Source) :
    drained (s := s) g q e (side (Shared50SparseIO.sourceRole entry)) =
      drained (s := s) g q e (y (e.symm (Shared50SparseIO.sourceLabel entry))) := by
  change label g q (Shared50ComplementFrames.output entry.val.2) = _
  rw [terminal_source_attachment g hcurrent q entry.val entry.property]
  change Geometry.liftLabel q (g.yOut (Labels.indicator (Shared50InitialLabels.source entry.val entry.property).val)) =
    Geometry.liftLabel q (g.yOut (indicator e (e.symm (Shared50SparseIO.sourceLabel entry))))
  simp only [indicator,Equiv.apply_symm_apply]
  rfl

section Nondegeneracy
variable [FiniteDimensional ℚ E] [FiniteDimensional ℚ H]

omit [FiniteDimensional ℚ E] in
private theorem triple_norm (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (T : Triple 50) : g.current (Labels.indicator T.val) (Labels.indicator T.val) ≠ 0 := by
  rw [hcurrent,Labels.rational_self T.val T.property]
  norm_num

private theorem complement_nd (U : Submodule ℚ Factor)
    (hU : ((Labels.rational 50).restrict U).Nondegenerate) :
    ((Labels.rational 50).restrict ((Labels.rational 50).orthogonal U)).Nondegenerate :=
  ProjectionRank.orthogonal_nondegenerate _ ⟨Labels.form_symm (1 / 9)⟩
    (Labels.rational_nondegenerate (by decide)) _ hU

variable (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50)
include hq

private theorem low_nd : ((g.liftedPairing D).restrict (low g q)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ g.common_nondegenerate
private theorem high_nd : ((g.liftedPairing D).restrict (high g q)).Nondegenerate :=
  g.liftLabel_nondegenerate D q hq _ g.full_nondegenerate

include hcurrent
private theorem reverseInput_nd (i : Fin 509194) :
    ((g.liftedPairing D).restrict (label g q (Shared50ComplementFrames.input i.val))).Nondegenerate :=
  label_nondegenerate g hcurrent D q hq _ (complement_nd _ (final_span_nondegenerate _))
private theorem reverseOutput_nd (i : Fin 509194) :
    ((g.liftedPairing D).restrict (label g q (Shared50ComplementFrames.output i.val))).Nondegenerate :=
  label_nondegenerate g hcurrent D q hq _ (complement_nd _ (initial_span_nondegenerate _))

private theorem injectFrame_nd (role : Fin 509194) :
    ((g.liftedPairing D).restrict (injectFrame g q e role)).Nondegenerate := by
  classical
  by_cases h : ∃ i, IsRead e role i
  · rw [injectFrame,dite_eq_left h]
    exact g.liftLabel_nondegenerate D q hq _ (g.xMiddle_nondegenerate _ (triple_norm g hcurrent _))
  · rw [injectFrame,dite_eq_right h]
    exact low_nd g D q hq

theorem injected_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (injected g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xMiddle_nondegenerate _ (triple_norm g hcurrent _))
  · exact low_nd g D q hq
  · exact injectFrame_nd g hcurrent D q hq e i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem reverseLoaded_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (reverseLoaded g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xMiddle_nondegenerate _ (triple_norm g hcurrent _))
  · exact low_nd g D q hq
  · exact reverseInput_nd g hcurrent D q hq i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem reverseComputed_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (reverseComputed g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact g.liftLabel_nondegenerate D q hq _ (g.xMiddle_nondegenerate _ (triple_norm g hcurrent _))
  · exact low_nd g D q hq
  · exact reverseOutput_nd g hcurrent D q hq i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem reverseGathered_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (reverseGathered g q r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact low_nd g D q hq
  · exact reverseOutput_nd g hcurrent D q hq i
  · exact high_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem reverseReturned_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (reverseReturned g q r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact low_nd g D q hq
  · exact reverseOutput_nd g hcurrent D q hq i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

theorem drained_nondegenerate (r : Wire n s) :
    ((g.liftedPairing D).restrict (drained g q e r)).Nondegenerate := by
  rcases r with i | i | i | i | i
  · exact high_nd g D q hq
  · exact g.liftLabel_nondegenerate D q hq _ (g.yOut_nondegenerate _ (triple_norm g hcurrent _))
  · exact reverseOutput_nd g hcurrent D q hq i
  · exact low_nd g D q hq
  · exact MotifLabels.bot_nondegenerate _

end Nondegeneracy
end IntegerMultBounds.Networks.Shared50OppositeLabels
