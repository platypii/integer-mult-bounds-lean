import IntegerMultBounds.Networks.Shared50OppositeLabels
import IntegerMultBounds.Networks.Shared50InvocationRank

/-! Exact finite frame history of the opposite invocation. It contains the
literal complemented inverse DAG trace between proved sparse input/output
attachments. Only the fifty central full-to-common returns lose dimension. -/

namespace IntegerMultBounds.Networks.Shared50OppositeRank

open scoped TensorProduct
open Circuit MotifLabels Shared50StageFrames Shared50LabeledInvocation Shared50OppositeLabels
open Shared50InvocationRank (align align_finish align_rel align_loss embedUpdates finish_embed_at finish_embed_outside edges_embed)

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code

variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup H] [Module ℚ H]

/-- Every actual reversed middle incidence in its original physical side slot. -/
def middleUpdates (g : Geometry ℚ E Factor) (q : H) : List (Wire n s × Space E H) :=
  embedUpdates (Shared50Invocation.sideEmbedding n 509194 50 s)
    (Shared50FiniteReverseTrace.reverse (label g q))

private theorem finish_side_banks {L : Type*} {n a c s : ℕ}
    (X Y : Fin n → L) (A : Fin a → L) (C : Fin c → L) (S : Fin s → L) (xs : List (Fin a × L)) :
    RankTrace.finish (banks X Y A C S) (embedUpdates (Shared50Invocation.sideEmbedding n a c s) xs) =
      banks X Y (RankTrace.finish A xs) C S := by
  funext r
  rcases r with i | i | i | i | i
  · exact finish_embed_outside _ _ _ (x i) (by intro j; change side j ≠ x i; simp [side,x])
  · exact finish_embed_outside _ _ _ (y i) (by intro j; change side j ≠ y i; simp [side,y])
  · exact finish_embed_at (Shared50Invocation.sideEmbedding n a c s) (banks X Y A C S) xs i
  · exact finish_embed_outside _ _ _ (center i) (by intro j; change side j ≠ center i; simp [side,center])
  · exact finish_embed_outside _ _ _ (spectator i) (by intro j; change side j ≠ spectator i; simp [side,spectator])

theorem middle_finish (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.finish (reverseLoaded (s := s) g q e) (middleUpdates g q) = reverseComputed g q e := by
  rw [middleUpdates,reverseLoaded,finish_side_banks,Shared50FiniteReverseTrace.reverse_finish]
  rfl

theorem middle_edges (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.edges (reverseLoaded (s := s) g q e) (middleUpdates g q) =
      (RankTrace.edges Shared50ComplementFrames.input Shared50ComplementFrames.updates).map
        (fun p => (label g q p.1,label g q p.2)) := by
  rw [middleUpdates,edges_embed]
  exact Shared50FiniteReverseTrace.reverse_edges (label g q)

/-- First three scalar blocks use `early`; J uses `injected`; the actual
inverse middle starts at `reverseLoaded`; R,G,V use the next three profiles;
the remaining four cleanup blocks use `output`. -/
noncomputable def updates (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    List (Wire n s × Space E H) :=
  align (early g q e) ++ align (injected g q e) ++ align (reverseLoaded g q e) ++ middleUpdates g q ++
    align (reverseGathered g q) ++ align (reverseReturned g q) ++ align (drained g q e) ++ align (output g q e)

theorem common_endpoints (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.finish (commonInput (s := s) g q e) (updates g q e) = output g q e := by
  simp only [updates,RankTrace.finish_append,align_finish,middle_finish]

theorem endpoints (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.finish (input (s := s) g q e) (updates g q e) = output g q e := by
  simp only [updates,RankTrace.finish_append,align_finish,middle_finish]

/-- Literal chronological edges; no readiness or rank bound is assumed. -/
theorem common_edges (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.edges (commonInput (s := s) g q e) (updates g q e) =
      RankTrace.edges (commonInput (s := s) g q e) (align (early g q e)) ++
      RankTrace.edges (early (s := s) g q e) (align (injected g q e)) ++
      RankTrace.edges (injected (s := s) g q e) (align (reverseLoaded g q e)) ++
      RankTrace.edges (reverseLoaded (s := s) g q e) (middleUpdates g q) ++
      RankTrace.edges (reverseComputed (s := s) g q e) (align (reverseGathered g q)) ++
      RankTrace.edges (reverseGathered (n := n) (s := s) g q) (align (reverseReturned g q)) ++
      RankTrace.edges (reverseReturned (s := s) g q) (align (drained g q e)) ++
      RankTrace.edges (drained (s := s) g q e) (align (output g q e)) := by
  simp only [updates,RankTrace.edges_append,RankTrace.finish_append,align_finish,middle_finish]

theorem common_comparable (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (commonInput (s := s) g q e) (updates g q e), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [common_edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (commonInput_le_early g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (early_le_injected g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (injected_le_reverseLoaded g q e) p hp)
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    exact Or.inl (label_mono g q (Shared50ComplementFrames.increasing old hold))
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (reverseComputed_le_gathered g q e) p hp)
  · exact Or.inr (align_rel (fun U V => V ≤ U) (fun _ => le_rfl) _ _ (reverseReturned_le_gathered g q) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (reverseReturned_le_drained g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (drained_le_output g q e) p hp)

section Nondegeneracy
variable [FiniteDimensional ℚ E] [FiniteDimensional ℚ H]

private theorem edges_property {ι L : Type*} [DecidableEq ι]
    (P : L → Prop) (current : ι → L) (xs : List (ι × L))
    (hc : ∀ i, P (current i)) (hx : ∀ p ∈ xs, P p.2) :
    ∀ p ∈ RankTrace.edges current xs, P p.1 ∧ P p.2 := by
  induction xs generalizing current with
  | nil => simp [RankTrace.edges]
  | cons pair xs ih =>
    obtain ⟨i,next⟩ := pair
    intro p hp
    simp only [RankTrace.edges,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hc i,hx (i,next) (by simp)⟩
    · apply ih (Function.update current i next) _ _ p hp
      · intro j
        by_cases h : j = i
        · subst j
          simp only [Function.update_self]
          exact hx (i,next) (by simp)
        · simpa [h] using hc j
      · intro pair hp
        exact hx pair (by simp [hp])

private theorem align_property {ι L : Type*} [DecidableEq ι] [Fintype ι]
    (P : L → Prop) (current desired : ι → L) (hc : ∀ i, P (current i))
    (hd : ∀ i, P (desired i)) :
    ∀ p ∈ RankTrace.edges current (align desired), P p.1 ∧ P p.2 := by
  apply edges_property P current _ hc
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact hd i

theorem common_nondegenerate (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (commonInput (s := s) g q e) (updates g q e),
      ((g.liftedPairing D).restrict p.1).Nondegenerate ∧ ((g.liftedPairing D).restrict p.2).Nondegenerate := by
  intro p hp
  rw [common_edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (commonInput_nondegenerate g hcurrent D q hq e) (early_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (early_nondegenerate g hcurrent D q hq e) (injected_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (injected_nondegenerate g hcurrent D q hq e) (reverseLoaded_nondegenerate g hcurrent D q hq e) p hp
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    have hn := Shared50ComplementFrames.nondegenerate old hold
    exact ⟨label_nondegenerate g hcurrent D q hq _ hn.1,label_nondegenerate g hcurrent D q hq _ hn.2⟩
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (reverseComputed_nondegenerate g hcurrent D q hq e) (reverseGathered_nondegenerate g hcurrent D q hq) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (reverseGathered_nondegenerate g hcurrent D q hq) (reverseReturned_nondegenerate g hcurrent D q hq) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (reverseReturned_nondegenerate g hcurrent D q hq) (drained_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _
      (drained_nondegenerate g hcurrent D q hq e) (output_nondegenerate g hcurrent D q hq e) p hp

private theorem align_loss_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (current desired : ι → Space E H) (hle : ∀ i, current i ≤ desired i) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U) current (align desired) = 0 := by
  rw [align_loss]
  apply Finset.sum_eq_zero
  intro i _
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (hle i))

theorem middle_loss_zero (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (reverseLoaded (s := s) g q e) (middleUpdates g q) = 0 := by
  unfold RankTrace.loss
  rw [middle_edges]
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (label_mono g q (Shared50ComplementFrames.increasing old hold)))

theorem central_loss (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (reverseGathered (n := n) (s := s) g q) (align (reverseReturned g q)) = 50 * Module.finrank ℚ Factor := by
  rw [align_loss]
  let d : Space E H → ℕ := fun U => Module.finrank ℚ U
  change (∑ r : Wire n s, (d (reverseGathered g q r) - d (reverseReturned g q r))) = _
  simp only [reverseGathered,reverseReturned,banks,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Nat.sub_self,Finset.sum_const_zero,zero_add,add_zero]
  have hh : d (high g q) - d (low g q) = Module.finrank ℚ Factor :=
    g.lifted_central_dimension_loss D q hq
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Exact loss for the complete opposite history with physical common-frame
scratch endpoints, independent of all initial register contents. -/
theorem common_loss (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H)
    (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (commonInput (s := s) g q e) (updates g q e) = 2500 := by
  simp only [updates,LabeledMotif.loss_append,RankTrace.finish_append,align_finish,middle_finish]
  rw [align_loss_zero _ _ (commonInput_le_early g q e),
    align_loss_zero _ _ (early_le_injected g q e),
    align_loss_zero _ _ (injected_le_reverseLoaded g q e),middle_loss_zero,
    align_loss_zero _ _ (reverseComputed_le_gathered g q e),central_loss g D q hq,
    align_loss_zero _ _ (reverseReturned_le_drained g q e),
    align_loss_zero _ _ (drained_le_output g q e)]
  simp [Factor]

end Nondegeneracy
end IntegerMultBounds.Networks.Shared50OppositeRank
