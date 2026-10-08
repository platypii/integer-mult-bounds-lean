import IntegerMultBounds.Networks.Shared50GlobalTrace
import IntegerMultBounds.Networks.Shared50OppositeRank

/-! Place local label updates on the actual sparse global invocation embeddings.
The local profiles are restrictions of the concrete stage profiles. Trace
premises remain explicit until the corresponding local histories are supplied. -/

namespace IntegerMultBounds.Networks.Shared50GlobalTracePlacement

noncomputable section
open scoped TensorProduct
open Circuit Shared50GlobalTrace
open Shared50GlobalBudget (Triple Address Side Control Invocation Scratch World)
open Shared50GlobalCircuit (localEmbedding localMap scratchKey)

variable {n : ℕ}

/-- The actual common-frame local source profile, already in cube coordinates. -/
def localInput (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) : Role n 509194 50 0 → Label :=
  banks (fun i => xInput j (GlobalCircuit.address j q (e i)))
    (fun i => yInput j (GlobalCircuit.address j q (e i)))
    (fun _ => common j q) (fun _ => common j q) Fin.elim0

def localOutput (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) : Role n 509194 50 0 → Label :=
  banks (fun i => xOutput j (GlobalCircuit.address j q (e i)))
    (fun i => yOutput j (GlobalCircuit.address j q (e i)))
    (fun _ => full j q) (fun _ => full j q) Fin.elim0

theorem scratchInput_at (j : Fin 3) (q : Triple × Triple) :
    scratchInput j (scratchKey j q) = common j q := by
  fin_cases j <;> simp [scratchInput,scratchKey,thirdKey]

theorem scratchOutput_at (j : Fin 3) (q : Triple × Triple) :
    scratchOutput j (scratchKey j q) = full j q := by
  fin_cases j <;> simp [scratchOutput,scratchKey,thirdKey]

/-- Restrict the physical global profile along the exact scalar invocation map. -/
theorem input_local (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    input j ∘ localEmbedding e j q = localInput e j q := by
  funext i
  rcases i with i | i | i | i | i
  · rfl
  · rfl
  · exact scratchInput_at j q
  · exact scratchInput_at j q
  · exact Fin.elim0 i

theorem output_local (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    output j ∘ localEmbedding e j q = localOutput e j q := by
  funext i
  rcases i with i | i | i | i | i
  · rfl
  · rfl
  · exact scratchOutput_at j q
  · exact scratchOutput_at j q
  · exact Fin.elim0 i

/-- Distinct invocation lines in one actual stage have disjoint physical roles. -/
theorem local_disjoint (e : Fin n ≃ Triple) (j : Fin 3) (q r : Triple × Triple) (hqr : q ≠ r)
    (i k : Role n 509194 50 0) : localEmbedding e j q i ≠ localEmbedding e j r k := by
  intro hh
  rcases i with i | i | i | i | i <;> rcases k with k | k | k | k | k <;>
    simp only [localEmbedding,localMap,Function.Embedding.coeFn_mk,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Prod.mk.injEq] at hh
  all_goals try exact Fin.elim0 i
  all_goals try exact Fin.elim0 k
  all_goals try exact hqr (by simpa using congrArg (GlobalCircuit.fixed j) hh)
  all_goals exact hqr (Shared50GlobalCircuit.scratchKey_injective j hh.1)

/-- Literal role placement of an already cube-valued local trace. -/
def place (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple)
    (xs : List (Role n 509194 50 0 × Label)) : List (World × Label) :=
  Shared50InvocationRank.embedUpdates (localEmbedding e j q) xs

theorem edges_place (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple)
    (xs : List (Role n 509194 50 0 × Label)) :
    RankTrace.edges (input j) (place e j q xs) = RankTrace.edges (localInput e j q) xs := by
  rw [place,Shared50InvocationRank.edges_embed,input_local]

/-- Placement preserves the complete actual downward dimension variation. -/
theorem loss_place (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple)
    (xs : List (Role n 509194 50 0 × Label)) :
    RankTrace.loss (fun U : Label => Module.finrank ℚ U) (input j) (place e j q xs) =
      RankTrace.loss (fun U : Label => Module.finrank ℚ U) (localInput e j q) xs := by
  unfold RankTrace.loss
  rw [edges_place]

section LabelMaps
variable {ι L M : Type*} [DecidableEq ι]

def mapLabels (f : L → M) (xs : List (ι × L)) : List (ι × M) :=
  xs.map (fun p => (p.1,f p.2))

theorem finish_mapLabels (f : L → M) (current : ι → L) (xs : List (ι × L)) :
    RankTrace.finish (fun i => f (current i)) (mapLabels f xs) =
      fun i => f (RankTrace.finish current xs i) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,next⟩ := p
    have he : Function.update (fun j => f (current j)) i (f next) =
        fun j => f (Function.update current i next j) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    simpa only [mapLabels,List.map_cons,RankTrace.finish,he] using ih (Function.update current i next)

theorem edges_mapLabels (f : L → M) (current : ι → L) (xs : List (ι × L)) :
    RankTrace.edges (fun i => f (current i)) (mapLabels f xs) =
      (RankTrace.edges current xs).map (fun p => (f p.1,f p.2)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨i,next⟩ := p
    have he : Function.update (fun j => f (current j)) i (f next) =
        fun j => f (Function.update current i next j) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    simp only [mapLabels,List.map_cons,RankTrace.edges,he]
    exact congrArg (List.cons (f (current i),f next)) (ih (Function.update current i next))

theorem loss_mapLabels (f : L → M) (dL : L → ℕ) (dM : M → ℕ)
    (hd : ∀ U, dM (f U) = dL U) (current : ι → L) (xs : List (ι × L)) :
    RankTrace.loss dM (fun i => f (current i)) (mapLabels f xs) = RankTrace.loss dL current xs := by
  simp only [RankTrace.loss,edges_mapLabels,List.map_map,Function.comp_def,hd]

end LabelMaps

open Shared50ReuseLabels (D vector vector_norm pairForm pair_vector_norm)

abbrev Factor := Shared50GlobalBudget.Base
abbrev FirstAmbient := (ℚ ⊗[ℚ] Factor) ⊗[ℚ] (Factor ⊗[ℚ] Factor)
abbrev SecondAmbient := (Factor ⊗[ℚ] Factor) ⊗[ℚ] Factor
abbrev ThirdAmbient := ((Factor ⊗[ℚ] Factor) ⊗[ℚ] Factor) ⊗[ℚ] ℚ

def firstMap (U : Submodule ℚ FirstAmbient) : Label := U.map StageLabels.firstEquiv.toLinearMap
def secondMap (U : Submodule ℚ SecondAmbient) : Label := U.map StageLabels.secondEquiv.toLinearMap
def thirdMap (U : Submodule ℚ ThirdAmbient) : Label := U.map StageLabels.thirdEquiv.toLinearMap

theorem firstMap_finrank (U : Submodule ℚ FirstAmbient) : Module.finrank ℚ (firstMap U) = Module.finrank ℚ U :=
  LabelTransport.finrank_label (K := ℚ) StageLabels.firstEquiv U

theorem secondMap_finrank (U : Submodule ℚ SecondAmbient) : Module.finrank ℚ (secondMap U) = Module.finrank ℚ U :=
  LabelTransport.finrank_label (K := ℚ) StageLabels.secondEquiv U

theorem thirdMap_finrank (U : Submodule ℚ ThirdAmbient) : Module.finrank ℚ (thirdMap U) = Module.finrank ℚ U :=
  (StageLabels.thirdEquiv (K := ℚ) (F := Factor)).finrank_map_eq U

theorem first_input_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => firstMap (Shared50LabeledInvocation.commonInput (s := 0) firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e i)) =
      localInput e 0 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

theorem first_output_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => firstMap (Shared50LabeledInvocation.output (s := 0) firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e i)) =
      localOutput e 0 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

def firstUpdates (e : Fin n ≃ Triple) (q : Triple × Triple) : List (Role n 509194 50 0 × Label) :=
  mapLabels firstMap (Shared50InvocationRank.updates (s := 0) firstGeometry (vector q.1 ⊗ₜ[ℚ] vector q.2) e)

theorem second_input_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => secondMap (Shared50LabeledInvocation.commonInput (s := 0) (secondGeometry q) (vector q.2) e i)) =
      localInput e 1 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

theorem second_output_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => secondMap (Shared50LabeledInvocation.output (s := 0) (secondGeometry q) (vector q.2) e i)) =
      localOutput e 1 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

def secondUpdates (e : Fin n ≃ Triple) (q : Triple × Triple) : List (Role n 509194 50 0 × Label) :=
  mapLabels secondMap (Shared50OppositeRank.updates (s := 0) (secondGeometry q) (vector q.2) e)

theorem third_input_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => thirdMap (Shared50LabeledInvocation.commonInput (s := 0) (thirdGeometry q) (1 : ℚ) e i)) =
      localInput e 2 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

theorem third_output_map (e : Fin n ≃ Triple) (q : Triple × Triple) :
    (fun i => thirdMap (Shared50LabeledInvocation.output (s := 0) (thirdGeometry q) (1 : ℚ) e i)) =
      localOutput e 2 q := by
  funext i
  rcases i with i | i | i | i | i <;> try rfl
  exact Fin.elim0 i

def thirdUpdates (e : Fin n ≃ Triple) (q : Triple × Triple) : List (Role n 509194 50 0 × Label) :=
  mapLabels thirdMap (Shared50InvocationRank.updates (s := 0) (thirdGeometry q) (1 : ℚ) e)

/-- The real forward / opposite inverse / forward local histories in cube coordinates. -/
def localUpdates (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    List (Role n 509194 50 0 × Label) :=
  if j = 0 then firstUpdates e q else if j = 1 then secondUpdates e q else thirdUpdates e q

theorem localUpdates_endpoints (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    RankTrace.finish (localInput e j q) (localUpdates e j q) = localOutput e j q := by
  fin_cases j
  · change RankTrace.finish (localInput e 0 q) (firstUpdates e q) = _
    rw [← first_input_map,firstUpdates,finish_mapLabels,Shared50InvocationRank.common_endpoints,first_output_map]
    rfl
  · change RankTrace.finish (localInput e 1 q) (secondUpdates e q) = _
    rw [← second_input_map,secondUpdates,finish_mapLabels,Shared50OppositeRank.common_endpoints,second_output_map]
    rfl
  · change RankTrace.finish (localInput e 2 q) (thirdUpdates e q) = _
    rw [← third_input_map,thirdUpdates,finish_mapLabels,Shared50InvocationRank.common_endpoints,third_output_map]
    rfl

/-- Tensor reassociation preserves the exact actual loss, including the fifty returns. -/
theorem localUpdates_loss (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    RankTrace.loss (fun U : Label => Module.finrank ℚ U) (localInput e j q) (localUpdates e j q) = 2500 := by
  fin_cases j
  · change RankTrace.loss _ (localInput e 0 q) (firstUpdates e q) = _
    rw [← first_input_map,firstUpdates,loss_mapLabels firstMap (fun U : Submodule ℚ FirstAmbient => Module.finrank ℚ U) _
      firstMap_finrank]
    exact Shared50InvocationRank.common_loss firstGeometry rfl pairForm _ (pair_vector_norm q.1 q.2) e
  · change RankTrace.loss _ (localInput e 1 q) (secondUpdates e q) = _
    rw [← second_input_map,secondUpdates,loss_mapLabels secondMap (fun U : Submodule ℚ SecondAmbient => Module.finrank ℚ U) _
      secondMap_finrank]
    exact Shared50OppositeRank.common_loss (secondGeometry q) D _ (vector_norm q.2) e
  · change RankTrace.loss _ (localInput e 2 q) (thirdUpdates e q) = _
    rw [← third_input_map,thirdUpdates,loss_mapLabels thirdMap (fun U : Submodule ℚ ThirdAmbient => Module.finrank ℚ U) _
      thirdMap_finrank]
    exact Shared50InvocationRank.common_loss (thirdGeometry q) rfl StageLabels.unitForm (1 : ℚ)
      (by simp [StageLabels.unitForm]) e

section Properties
variable {ι L M : Type*} [DecidableEq ι]

theorem predicate_mapLabels (f : L → M) (P : L → Prop) (Q : M → Prop)
    (hf : ∀ U, P U → Q (f U)) (current : ι → L) (xs : List (ι × L))
    (hc : ∀ p ∈ RankTrace.edges current xs, P p.1 ∧ P p.2) :
    ∀ p ∈ RankTrace.edges (fun i => f (current i)) (mapLabels f xs), Q p.1 ∧ Q p.2 := by
  intro p hp
  rw [edges_mapLabels] at hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact ⟨hf r.1 (hc r hr).1,hf r.2 (hc r hr).2⟩

theorem comparable_mapLabels [Preorder L] [Preorder M] (f : L → M) (hf : Monotone f)
    (current : ι → L) (xs : List (ι × L))
    (hc : ∀ p ∈ RankTrace.edges current xs, p.1 ≤ p.2 ∨ p.2 ≤ p.1) :
    ∀ p ∈ RankTrace.edges (fun i => f (current i)) (mapLabels f xs), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [edges_mapLabels] at hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact (hc r hr).elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hf h))

end Properties

theorem localUpdates_comparable (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    ∀ p ∈ RankTrace.edges (localInput e j q) (localUpdates e j q), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  fin_cases j
  · change ∀ p ∈ RankTrace.edges (localInput e 0 q) (firstUpdates e q), p.1 ≤ p.2 ∨ p.2 ≤ p.1
    rw [← first_input_map,firstUpdates]
    apply comparable_mapLabels firstMap (fun _ _ h => Submodule.map_mono h)
    exact Shared50InvocationRank.common_comparable firstGeometry rfl (vector q.1 ⊗ₜ[ℚ] vector q.2) e
  · change ∀ p ∈ RankTrace.edges (localInput e 1 q) (secondUpdates e q), p.1 ≤ p.2 ∨ p.2 ≤ p.1
    rw [← second_input_map,secondUpdates]
    apply comparable_mapLabels secondMap (fun _ _ h => Submodule.map_mono h)
    exact Shared50OppositeRank.common_comparable (secondGeometry q) (vector q.2) e
  · change ∀ p ∈ RankTrace.edges (localInput e 2 q) (thirdUpdates e q), p.1 ≤ p.2 ∨ p.2 ≤ p.1
    rw [← third_input_map,thirdUpdates]
    apply comparable_mapLabels thirdMap (fun _ _ h => Submodule.map_mono h)
    exact Shared50InvocationRank.common_comparable (thirdGeometry q) rfl (1 : ℚ) e

end
end IntegerMultBounds.Networks.Shared50GlobalTracePlacement
