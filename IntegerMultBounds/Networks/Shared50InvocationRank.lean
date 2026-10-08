import IntegerMultBounds.Networks.Shared50LabeledInvocation
import IntegerMultBounds.Networks.Shared50FiniteTrace

/-! Exact rank-loss accounting for the actual finite forward invocation. The
history contains explicit scalar-block boundary alignments and all actual DAG
incidences. Its only downward transitions are the fifty central returns. -/

namespace IntegerMultBounds.Networks.Shared50InvocationRank

open scoped TensorProduct
open Circuit MotifLabels Shared50StageFrames Shared50LabeledInvocation

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code

section Embedding
variable {ι κ L : Type*} [DecidableEq ι] [DecidableEq κ]

def embedUpdates (e : ι ↪ κ) (xs : List (ι × L)) : List (κ × L) :=
  xs.map (fun p => (e p.1,p.2))

theorem finish_embed_at (e : ι ↪ κ) (current : κ → L) (xs : List (ι × L)) (i : ι) :
    RankTrace.finish current (embedUpdates e xs) (e i) = RankTrace.finish (current ∘ e) xs i := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨j,next⟩ := p
    have he : Function.update current (e j) next ∘ e = Function.update (current ∘ e) j next := by
      funext k
      simp [Function.comp_def,Function.update_apply,e.injective.eq_iff]
    simpa only [embedUpdates,List.map_cons,RankTrace.finish,he] using ih (Function.update current (e j) next)

omit [DecidableEq ι] in
theorem finish_embed_outside (e : ι ↪ κ) (current : κ → L) (xs : List (ι × L))
    (i : κ) (hi : ∀ j, e j ≠ i) : RankTrace.finish current (embedUpdates e xs) i = current i := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨j,next⟩ := p
    simpa only [embedUpdates,List.map_cons,RankTrace.finish,Function.update_of_ne (Ne.symm (hi j))] using
      ih (Function.update current (e j) next)

theorem edges_embed (e : ι ↪ κ) (current : κ → L) (xs : List (ι × L)) :
    RankTrace.edges current (embedUpdates e xs) = RankTrace.edges (current ∘ e) xs := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨j,next⟩ := p
    have he : Function.update current (e j) next ∘ e = Function.update (current ∘ e) j next := by
      funext k
      simp [Function.comp_def,Function.update_apply,e.injective.eq_iff]
    simp only [embedUpdates,List.map_cons,RankTrace.edges]
    exact congrArg (List.cons (current (e j),next)) ((ih _).trans (congrArg (fun c => RankTrace.edges c xs) he))
end Embedding

section Alignments
variable {ι L : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual local role is explicitly aligned at a scalar-block boundary. -/
noncomputable def align (desired : ι → L) : List (ι × L) :=
  (Finset.univ.toList).map (fun i => (i,desired i))

theorem align_finish (current desired : ι → L) : RankTrace.finish current (align desired) = desired := by
  funext i
  simp [align,RankTrace.finish_align]

theorem align_rel (rel : L → L → Prop) (hrefl : ∀ U, rel U U)
    (current desired : ι → L) (h : ∀ i, rel (current i) (desired i)) :
    ∀ p ∈ RankTrace.edges current (align desired), rel p.1 p.2 :=
  LabeledMotif.edges_endpoints_rel rel hrefl current desired _ (fun i _ => h i)

theorem align_loss (d : L → ℕ) (current desired : ι → L) :
    RankTrace.loss d current (align desired) = ∑ i, (d (current i) - d (desired i)) := by
  rw [align,LabeledMotif.loss_align]
  simp

end Alignments

variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup H] [Module ℚ H]

/-- All actual forward DAG incidences, embedded in the physical side bank. -/
def middleUpdates (g : Geometry ℚ E Factor) (q : H) : List (Wire n s × Space E H) :=
  embedUpdates (Shared50Invocation.sideEmbedding n 509194 50 s)
    (Shared50FiniteTrace.forward (label g q))

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

theorem middle_finish (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.finish (returned (n := n) (s := s) g q) (middleUpdates g q) = computed g q := by
  rw [middleUpdates,returned,finish_side_banks,Shared50FiniteTrace.forward_finish]
  rfl

theorem middle_edges (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.edges (returned (n := n) (s := s) g q) (middleUpdates g q) =
      (RankTrace.edges Shared50Frames.initialLabels Shared50Frames.updates).map
        (fun p => (label g q p.1,label g q p.2)) := by
  rw [middleUpdates,edges_embed]
  exact Shared50FiniteTrace.forward_edges (label g q)

/-- Chronological frame changes in the literal twelve-block scalar schedule:
early mixers, source loading, gather, central return, actual middle DAG,
readout and final cleanup. Scalar-only blocks leave these profiles unchanged. -/
noncomputable def updates (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    List (Wire n s × Space E H) :=
  align (early g q e) ++ align (loaded g q e) ++ align (gathered g q) ++ align (returned g q) ++
    middleUpdates g q ++ align (readout g q e) ++ align (output g q e)

theorem endpoints (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.finish (input (s := s) g q e) (updates g q e) = output g q e := by
  simp only [updates,RankTrace.finish_append,align_finish,middle_finish]

/-- The exact edge list splits at the seven real alignment/middle boundaries. -/
theorem edges (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.edges (input (s := s) g q e) (updates g q e) =
      RankTrace.edges (input (n := n) (s := s) g q e) (align (early (n := n) (s := s) g q e)) ++
      RankTrace.edges (early (n := n) (s := s) g q e) (align (loaded (n := n) (s := s) g q e)) ++
      RankTrace.edges (loaded (n := n) (s := s) g q e) (align (gathered (n := n) (s := s) g q)) ++
      RankTrace.edges (gathered (n := n) (s := s) g q) (align (returned (n := n) (s := s) g q)) ++
      RankTrace.edges (returned (n := n) (s := s) g q) (middleUpdates g q) ++
      RankTrace.edges (computed (n := n) (s := s) g q) (align (readout (n := n) (s := s) g q e)) ++
      RankTrace.edges (readout (n := n) (s := s) g q e) (align (output (n := n) (s := s) g q e)) := by
  simp only [updates,RankTrace.edges_append,RankTrace.finish_append,align_finish,middle_finish]

/-- All consecutive labels are nested; decreasing central edges are explicit. -/
theorem comparable (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (input (s := s) g q e) (updates g q e), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (input_le_early g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (early_le_loaded g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (loaded_le_gathered g q e) p hp)
  · exact Or.inr (align_rel (fun U V => V ≤ U) (fun _ => le_rfl) _ _ (returned_le_gathered g q) p hp)
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    exact Or.inl (label_mono g q (Shared50Frames.increasing old hold))
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (computed_le_readout g hcurrent q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (readout_le_output g q e) p hp)

theorem common_endpoints (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.finish (commonInput (s := s) g q e) (updates g q e) = output g q e := by
  simp only [updates,RankTrace.finish_append,align_finish,middle_finish]

theorem common_edges (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.edges (commonInput (s := s) g q e) (updates g q e) =
      RankTrace.edges (commonInput (n := n) (s := s) g q e) (align (early (n := n) (s := s) g q e)) ++
      RankTrace.edges (early (n := n) (s := s) g q e) (align (loaded (n := n) (s := s) g q e)) ++
      RankTrace.edges (loaded (n := n) (s := s) g q e) (align (gathered (n := n) (s := s) g q)) ++
      RankTrace.edges (gathered (n := n) (s := s) g q) (align (returned (n := n) (s := s) g q)) ++
      RankTrace.edges (returned (n := n) (s := s) g q) (middleUpdates g q) ++
      RankTrace.edges (computed (n := n) (s := s) g q) (align (readout (n := n) (s := s) g q e)) ++
      RankTrace.edges (readout (n := n) (s := s) g q e) (align (output (n := n) (s := s) g q e)) := by
  simp only [updates,RankTrace.edges_append,RankTrace.finish_append,align_finish,middle_finish]

theorem common_comparable (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (commonInput (s := s) g q e) (updates g q e), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [common_edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (commonInput_le_early g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (early_le_loaded g q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (loaded_le_gathered g q e) p hp)
  · exact Or.inr (align_rel (fun U V => V ≤ U) (fun _ => le_rfl) _ _ (returned_le_gathered g q) p hp)
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    exact Or.inl (label_mono g q (Shared50Frames.increasing old hold))
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (computed_le_readout g hcurrent q e) p hp)
  · exact Or.inl (align_rel (· ≤ ·) (fun _ => le_rfl) _ _ (readout_le_output g q e) p hp)

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

theorem nondegenerate (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (input (s := s) g q e) (updates g q e),
      ((g.liftedPairing D).restrict p.1).Nondegenerate ∧ ((g.liftedPairing D).restrict p.2).Nondegenerate := by
  intro p hp
  rw [edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (input_nondegenerate g hcurrent D q hq e)
      (early_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (early_nondegenerate g hcurrent D q hq e)
      (loaded_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (loaded_nondegenerate g hcurrent D q hq e)
      (gathered_nondegenerate g hcurrent D q hq) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (gathered_nondegenerate g hcurrent D q hq)
      (returned_nondegenerate g hcurrent D q hq) p hp
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    have hn := Shared50Frames.nondegenerate old hold
    exact ⟨label_nondegenerate g hcurrent D q hq _ hn.1,label_nondegenerate g hcurrent D q hq _ hn.2⟩
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (computed_nondegenerate g hcurrent D q hq)
      (readout_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (readout_nondegenerate g hcurrent D q hq e)
      (output_nondegenerate g hcurrent D q hq e) p hp

private theorem align_loss_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (current desired : ι → Space E H) (hle : ∀ i, current i ≤ desired i) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U) current (align desired) = 0 := by
  rw [align_loss]
  apply Finset.sum_eq_zero
  intro i _
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (hle i))

theorem middle_loss_zero (g : Geometry ℚ E Factor) (q : H) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (returned (n := n) (s := s) g q) (middleUpdates g q) = 0 := by
  unfold RankTrace.loss
  rw [middle_edges]
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (label_mono g q (Shared50Frames.increasing old hold)))

/-- The sole decreasing block loses exactly one current-factor dimension on
 each of the fifty actual central registers, independent of scratch contents. -/
theorem central_loss (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (gathered (n := n) (s := s) g q) (align (returned g q)) = 50 * Module.finrank ℚ Factor := by
  rw [align_loss]
  let d : Space E H → ℕ := fun U => Module.finrank ℚ U
  change (∑ r : Wire n s, (d (gathered g q r) - d (returned g q r))) = _
  simp only [gathered,returned,banks,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Nat.sub_self,Finset.sum_const_zero,zero_add,add_zero]
  have hh : d (high g q) - d (low g q) = Module.finrank ℚ Factor :=
    g.lifted_central_dimension_loss D q hq
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Exact total loss of the whole concrete forward invocation history,
including the data/auxiliary endpoints and every actual middle incidence. -/
theorem loss (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (input (s := s) g q e) (updates g q e) = 2500 := by
  simp only [updates,LabeledMotif.loss_append,RankTrace.finish_append,align_finish,middle_finish]
  rw [align_loss_zero _ _ (input_le_early g q e),
    align_loss_zero _ _ (early_le_loaded g q e),
    align_loss_zero _ _ (loaded_le_gathered g q e),central_loss g D q hq,middle_loss_zero,
    align_loss_zero _ _ (computed_le_readout g hcurrent q e),
    align_loss_zero _ _ (readout_le_output g q e)]
  simp [Factor]

theorem common_nondegenerate (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    ∀ p ∈ RankTrace.edges (commonInput (s := s) g q e) (updates g q e),
      ((g.liftedPairing D).restrict p.1).Nondegenerate ∧ ((g.liftedPairing D).restrict p.2).Nondegenerate := by
  intro p hp
  rw [common_edges] at hp
  simp only [List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (commonInput_nondegenerate g hcurrent D q hq e)
      (early_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (early_nondegenerate g hcurrent D q hq e)
      (loaded_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (loaded_nondegenerate g hcurrent D q hq e)
      (gathered_nondegenerate g hcurrent D q hq) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (gathered_nondegenerate g hcurrent D q hq)
      (returned_nondegenerate g hcurrent D q hq) p hp
  · rw [middle_edges] at hp
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hp
    have hn := Shared50Frames.nondegenerate old hold
    exact ⟨label_nondegenerate g hcurrent D q hq _ hn.1,label_nondegenerate g hcurrent D q hq _ hn.2⟩
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (computed_nondegenerate g hcurrent D q hq)
      (readout_nondegenerate g hcurrent D q hq e) p hp
  · exact align_property (fun U : Space E H => ((g.liftedPairing D).restrict U).Nondegenerate) _ _ (readout_nondegenerate g hcurrent D q hq e)
      (output_nondegenerate g hcurrent D q hq e) p hp

theorem common_loss (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ NeighborCounts.Triple 50) :
    RankTrace.loss (fun U : Space E H => Module.finrank ℚ U)
      (commonInput (s := s) g q e) (updates g q e) = 2500 := by
  simp only [updates,LabeledMotif.loss_append,RankTrace.finish_append,align_finish,middle_finish]
  rw [align_loss_zero _ _ (commonInput_le_early g q e),
    align_loss_zero _ _ (early_le_loaded g q e),
    align_loss_zero _ _ (loaded_le_gathered g q e),central_loss g D q hq,middle_loss_zero,
    align_loss_zero _ _ (computed_le_readout g hcurrent q e),
    align_loss_zero _ _ (readout_le_output g q e)]
  simp [Factor]

end Nondegeneracy

end IntegerMultBounds.Networks.Shared50InvocationRank
