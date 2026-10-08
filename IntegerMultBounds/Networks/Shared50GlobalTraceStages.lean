import IntegerMultBounds.Networks.Shared50GlobalTraceNondegenerate

/-! Chronological composition of the actual local histories on the reused
physical world. Each stage enumerates exactly the scalar schedule's coordinate
lines; disjointness within a stage preserves every unprocessed local profile. -/

namespace IntegerMultBounds.Networks.Shared50GlobalTraceStages

noncomputable section
open Circuit Shared50GlobalTrace Shared50GlobalTracePlacement
open Shared50GlobalBudget (Triple Address Side Control Invocation Scratch World)
open Shared50GlobalCircuit (localEmbedding localMap)

variable {n : ℕ}

abbrev dimension (U : Label) := Module.finrank ℚ U

def invocationUpdates (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) : List (World × Label) :=
  place e j q (localUpdates e j q)

def partialStage (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple)) : List (World × Label) :=
  qs.flatMap (invocationUpdates e j)

def stageUpdates (e : Fin n ≃ Triple) (j : Fin 3) : List (World × Label) :=
  partialStage e j (GlobalCircuit.keys e)

def Matches (e : Fin n ≃ Triple) (j : Fin 3) (current : Profile) (qs : List (Triple × Triple)) : Prop :=
  ∀ q ∈ qs, current ∘ localEmbedding e j q = localInput e j q

theorem invocation_edges (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hc : current ∘ localEmbedding e j q = localInput e j q) :
    RankTrace.edges current (invocationUpdates e j q) = RankTrace.edges (localInput e j q) (localUpdates e j q) := by
  rw [invocationUpdates,place,Shared50InvocationRank.edges_embed,hc]

theorem invocation_finish_local (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hc : current ∘ localEmbedding e j q = localInput e j q) :
    RankTrace.finish current (invocationUpdates e j q) ∘ localEmbedding e j q = localOutput e j q := by
  funext i
  rw [Function.comp_apply,invocationUpdates,place,Shared50InvocationRank.finish_embed_at,hc,localUpdates_endpoints]

theorem invocation_finish_outside (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (w : World) (hw : ∀ i, localEmbedding e j q i ≠ w) :
    RankTrace.finish current (invocationUpdates e j q) w = current w :=
  Shared50InvocationRank.finish_embed_outside _ _ _ w hw

/-- A processed coordinate line leaves every different line's full local profile untouched. -/
theorem invocation_finish_other (e : Fin n ≃ Triple) (j : Fin 3) (q r : Triple × Triple)
    (hqr : q ≠ r) (current : Profile) :
    RankTrace.finish current (invocationUpdates e j q) ∘ localEmbedding e j r = current ∘ localEmbedding e j r := by
  funext i
  exact invocation_finish_outside e j q current _ (fun k => local_disjoint e j q r hqr k i)

theorem matches_after_head (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple)
    (qs : List (Triple × Triple)) (current : Profile) (hq : q ∉ qs)
    (hc : Matches e j current (q :: qs)) :
    Matches e j (RankTrace.finish current (invocationUpdates e j q)) qs := by
  intro r hr
  rw [invocation_finish_other e j q r (by intro he; subst r; exact hq hr)]
  exact hc r (List.mem_cons_of_mem q hr)

theorem partialStage_finish_other (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (r : Triple × Triple) (hr : r ∉ qs) (current : Profile) :
    RankTrace.finish current (partialStage e j qs) ∘ localEmbedding e j r = current ∘ localEmbedding e j r := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    have hn : r ≠ q ∧ r ∉ qs := by simpa only [List.mem_cons,not_or] using hr
    simp only [partialStage,List.flatMap_cons,RankTrace.finish_append]
    rw [show RankTrace.finish (RankTrace.finish current (invocationUpdates e j q))
      (List.flatMap (invocationUpdates e j) qs) ∘ localEmbedding e j r = _ from ih hn.2 _]
    exact invocation_finish_other e j q r (Ne.symm hn.1) current

theorem partialStage_finish_local (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (hqs : qs.Nodup) (current : Profile) (hc : Matches e j current qs)
    (r : Triple × Triple) (hr : r ∈ qs) :
    RankTrace.finish current (partialStage e j qs) ∘ localEmbedding e j r = localOutput e j r := by
  induction qs generalizing current with
  | nil => simp at hr
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hqs
    simp only [partialStage,List.flatMap_cons,RankTrace.finish_append]
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      rw [show RankTrace.finish (RankTrace.finish current (invocationUpdates e j q))
        (List.flatMap (invocationUpdates e j) qs) ∘ localEmbedding e j q = _ from
          partialStage_finish_other e j qs q hn _]
      exact invocation_finish_local e j q current (hc q (List.mem_cons_self))
    · exact ih ht _ (matches_after_head e j q qs current hn hc) hr

theorem partialStage_finish_outside (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (current : Profile) (w : World) (hw : ∀ q ∈ qs, ∀ i, localEmbedding e j q i ≠ w) :
    RankTrace.finish current (partialStage e j qs) w = current w := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    simp only [partialStage,List.flatMap_cons,RankTrace.finish_append]
    rw [show RankTrace.finish (RankTrace.finish current (invocationUpdates e j q))
      (List.flatMap (invocationUpdates e j) qs) w = _ from
        ih _ (fun r hr => hw r (List.mem_cons_of_mem q hr))]
    exact invocation_finish_outside e j q current w (hw q List.mem_cons_self)

/-- Every role outside this stage's invocation family has identical endpoint labels. -/
theorem input_output_outside (e : Fin n ≃ Triple) (j : Fin 3) (w : World)
    (hw : ∀ q i, localEmbedding e j q i ≠ w) : input j w = output j w := by
  rcases w with b | b | ⟨⟨bank,q⟩,slot⟩
  · exfalso
    apply hw (GlobalCircuit.fixed j b) (x (e.symm (GlobalCircuit.varying j b)))
    simp [localEmbedding,localMap,x]
  · exfalso
    apply hw (GlobalCircuit.fixed j b) (y (e.symm (GlobalCircuit.varying j b)))
    simp [localEmbedding,localMap,y]
  · fin_cases j <;> fin_cases bank <;> try rfl
    · exfalso
      cases slot with
      | inl a => exact hw q (side a) rfl
      | inr c => exact hw q (center c) rfl
    · exfalso
      cases slot with
      | inl a => exact hw q (side a) rfl
      | inr c => exact hw q (center c) rfl
    · exfalso
      cases slot with
      | inl a =>
        apply hw (thirdKey q) (side a)
        simp [localEmbedding,localMap,side,thirdKey,Shared50GlobalCircuit.scratchKey]
      | inr c =>
        apply hw (thirdKey q) (center c)
        simp [localEmbedding,localMap,center,thirdKey,Shared50GlobalCircuit.scratchKey]

/-- Every coordinate line finishes at the actual next stage profile. -/
theorem stage_finish (e : Fin n ≃ Triple) (j : Fin 3) :
    RankTrace.finish (input j) (stageUpdates e j) = output j := by
  funext w
  by_cases hw : ∃ q i, localEmbedding e j q i = w
  · obtain ⟨q,i,rfl⟩ := hw
    exact (congrFun (partialStage_finish_local e j (GlobalCircuit.keys e)
      (GlobalCircuit.keys_nodup e) (input j) (fun q _ => input_local e j q)
      q (GlobalCircuit.mem_keys e q)) i).trans (congrFun (output_local e j q) i).symm
  · have hn : ∀ q i, localEmbedding e j q i ≠ w := by simpa using hw
    exact (partialStage_finish_outside e j (GlobalCircuit.keys e) (input j) w
      (fun q _ => hn q)).trans (input_output_outside e j w hn)

theorem invocation_loss (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) (current : Profile)
    (hc : current ∘ localEmbedding e j q = localInput e j q) :
    RankTrace.loss dimension current (invocationUpdates e j q) = 2500 := by
  unfold RankTrace.loss
  rw [invocation_edges e j q current hc]
  exact localUpdates_loss e j q

theorem partialStage_loss (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (hqs : qs.Nodup) (current : Profile) (hc : Matches e j current qs) :
    RankTrace.loss dimension current (partialStage e j qs) = qs.length * 2500 := by
  induction qs generalizing current with
  | nil => simp [partialStage,RankTrace.loss,RankTrace.edges]
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hqs
    simp only [partialStage,List.flatMap_cons,LabeledMotif.loss_append]
    rw [invocation_loss e j q current (hc q List.mem_cons_self)]
    rw [show RankTrace.loss dimension (RankTrace.finish current (invocationUpdates e j q))
      (List.flatMap (invocationUpdates e j) qs) = _ from
        ih ht _ (matches_after_head e j q qs current hn hc)]
    simp only [List.length_cons]
    omega

theorem stage_loss (e : Fin n ≃ Triple) (j : Fin 3) :
    RankTrace.loss dimension (input j) (stageUpdates e j) = n ^ 2 * 2500 := by
  rw [stageUpdates,partialStage_loss e j _ (GlobalCircuit.keys_nodup e) _
    (fun q _ => input_local e j q),GlobalCircuit.keys_length]
  ring

theorem partialStage_comparable (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (hqs : qs.Nodup) (current : Profile) (hc : Matches e j current qs) :
    ∀ p ∈ RankTrace.edges current (partialStage e j qs), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  induction qs generalizing current with
  | nil => simp [partialStage,RankTrace.edges]
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hqs
    intro p hp
    simp only [partialStage,List.flatMap_cons,RankTrace.edges_append,List.mem_append] at hp
    rcases hp with hp | hp
    · rw [invocation_edges e j q current (hc q List.mem_cons_self)] at hp
      exact localUpdates_comparable e j q p hp
    · exact ih ht _ (matches_after_head e j q qs current hn hc) p hp

theorem stage_comparable (e : Fin n ≃ Triple) (j : Fin 3) :
    ∀ p ∈ RankTrace.edges (input j) (stageUpdates e j), p.1 ≤ p.2 ∨ p.2 ≤ p.1 :=
  partialStage_comparable e j _ (GlobalCircuit.keys_nodup e) _ (fun q _ => input_local e j q)

theorem partialStage_nondegenerate (e : Fin n ≃ Triple) (j : Fin 3) (qs : List (Triple × Triple))
    (hqs : qs.Nodup) (current : Profile) (hc : Matches e j current qs) :
    ∀ p ∈ RankTrace.edges current (partialStage e j qs),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate := by
  induction qs generalizing current with
  | nil => simp [partialStage,RankTrace.edges]
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hqs
    intro p hp
    simp only [partialStage,List.flatMap_cons,RankTrace.edges_append,List.mem_append] at hp
    rcases hp with hp | hp
    · rw [invocation_edges e j q current (hc q List.mem_cons_self)] at hp
      exact localUpdates_nondegenerate e j q p hp
    · exact ih ht _ (matches_after_head e j q qs current hn hc) p hp

theorem stage_nondegenerate (e : Fin n ≃ Triple) (j : Fin 3) :
    ∀ p ∈ RankTrace.edges (input j) (stageUpdates e j),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate :=
  partialStage_nondegenerate e j _ (GlobalCircuit.keys_nodup e) _ (fun q _ => input_local e j q)

/-- Chronological global history: four proved attachment boundaries and the
same three ordered invocation-key lists as the actual sparse scalar program. -/
def trace (e : Fin n ≃ Triple) : List (World × Label) :=
  boundaryUpdates 0 ++ stageUpdates e 0 ++ boundaryUpdates 1 ++ stageUpdates e 1 ++
    boundaryUpdates 2 ++ stageUpdates e 2 ++ boundaryUpdates 3

theorem trace_finish (e : Fin n ≃ Triple) : RankTrace.finish source (trace e) = sink := by
  have h0 : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  have h3 : RankTrace.finish (output 2) (boundaryUpdates 3) = sink := boundary_finish 3
  simp only [trace,RankTrace.finish_append,h0,h1,h2,h3,stage_finish]

theorem trace_loss (e : Fin n ≃ Triple) :
    RankTrace.loss dimension source (trace e) = 3 * n ^ 2 * 2500 := by
  have h0 : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  have h3 : RankTrace.loss dimension source (boundaryUpdates 0) = 0 := boundary_loss_zero 0
  have h4 : RankTrace.loss dimension (output 0) (boundaryUpdates 1) = 0 := boundary_loss_zero 1
  have h5 : RankTrace.loss dimension (output 1) (boundaryUpdates 2) = 0 := boundary_loss_zero 2
  have h6 : RankTrace.loss dimension (output 2) (boundaryUpdates 3) = 0 := boundary_loss_zero 3
  simp only [trace,LabeledMotif.loss_append,RankTrace.finish_append,h0,h1,h2,h3,h4,h5,h6,
    stage_finish,stage_loss]
  ring

theorem trace_comparable (e : Fin n ≃ Triple) :
    ∀ p ∈ RankTrace.edges source (trace e), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  have h0 : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  intro p hp
  simp only [trace,RankTrace.edges_append,RankTrace.finish_append,h0,h1,h2,stage_finish,List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact Or.inl (boundary_edges_increasing 0 p hp)
  · exact stage_comparable e 0 p hp
  · exact Or.inl (boundary_edges_increasing 1 p hp)
  · exact stage_comparable e 1 p hp
  · exact Or.inl (boundary_edges_increasing 2 p hp)
  · exact stage_comparable e 2 p hp
  · exact Or.inl (boundary_edges_increasing 3 p hp)

theorem trace_nondegenerate (e : Fin n ≃ Triple) :
    ∀ p ∈ RankTrace.edges source (trace e),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate := by
  have h0 : RankTrace.finish source (boundaryUpdates 0) = input 0 := boundary_finish 0
  have h1 : RankTrace.finish (output 0) (boundaryUpdates 1) = input 1 := boundary_finish 1
  have h2 : RankTrace.finish (output 1) (boundaryUpdates 2) = input 2 := boundary_finish 2
  intro p hp
  simp only [trace,RankTrace.edges_append,RankTrace.finish_append,h0,h1,h2,stage_finish,List.mem_append] at hp
  rcases hp with (((((hp | hp) | hp) | hp) | hp) | hp) | hp
  · exact boundary_edges_nondegenerate 0 p hp
  · exact stage_nondegenerate e 0 p hp
  · exact boundary_edges_nondegenerate 1 p hp
  · exact stage_nondegenerate e 1 p hp
  · exact boundary_edges_nondegenerate 2 p hp
  · exact stage_nondegenerate e 2 p hp
  · exact boundary_edges_nondegenerate 3 p hp

private theorem updates_predicate_of_edges {ι L : Type*} [DecidableEq ι]
    (P : L → Prop) (current : ι → L) (xs : List (ι × L))
    (hp : ∀ p ∈ RankTrace.edges current xs, P p.2) : ∀ u ∈ xs, P u.2 := by
  induction xs generalizing current with
  | nil => simp
  | cons u xs ih =>
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact hp (current u.1,u.2) (List.mem_cons_self)
    · exact ih (Function.update current u.1 u.2)
        (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) v hv

theorem trace_updates_nondegenerate (e : Fin n ≃ Triple) :
    ∀ u ∈ trace e, (Shared50ReuseLabels.cubeForm.restrict u.2).Nondegenerate :=
  updates_predicate_of_edges (fun U : Label => (Shared50ReuseLabels.cubeForm.restrict U).Nondegenerate)
    source (trace e) (fun p hp => (trace_nondegenerate e p hp).2)

/-- The fixed fifty-point global trace uses the same enumeration as program50. -/
def trace50 := trace Shared50GlobalCircuit.enumeration

theorem trace50_finish : RankTrace.finish source trace50 = sink := trace_finish _

theorem trace50_loss : RankTrace.loss dimension source trace50 = Shared50Parameters.L := by
  have hn : 3 * 19600 ^ 2 * 2500 = Shared50Parameters.L := by
    rw [Shared50Parameters.loss_count]
    norm_num
  exact (trace_loss Shared50GlobalCircuit.enumeration).trans hn

end
end IntegerMultBounds.Networks.Shared50GlobalTraceStages
