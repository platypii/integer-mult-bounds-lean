import IntegerMultBounds.Networks.Shared50GlobalTracePlacement

/-! Nondegeneracy of the concrete transported local invocation histories. -/
namespace IntegerMultBounds.Networks.Shared50GlobalTracePlacement
set_option synthInstance.maxSize 2048

noncomputable section
open scoped TensorProduct
open Shared50GlobalTrace
open Shared50GlobalBudget (Triple)
open Shared50ReuseLabels (D vector vector_norm pairForm pair_vector_norm)
variable {n : ℕ}

private theorem third_transport {F : Type*} [AddCommGroup F] [Module ℚ F]
    (B : LinearMap.BilinForm ℚ F) (U : Submodule ℚ (((F ⊗[ℚ] F) ⊗[ℚ] F) ⊗[ℚ] ℚ))
    (hU : ((TensorSubspace.form (TensorSubspace.form (TensorSubspace.form B B) B)
      StageLabels.unitForm).restrict U).Nondegenerate) :
    ((TensorSubspace.form B (TensorSubspace.form B B)).restrict
      (U.map (StageLabels.thirdEquiv (K := ℚ) (F := F)).toLinearMap)).Nondegenerate := by
  apply LabelTransport.nondegenerate
    (TensorSubspace.form (TensorSubspace.form (TensorSubspace.form B B) B) StageLabels.unitForm)
    (TensorSubspace.form B (TensorSubspace.form B B))
    (StageLabels.thirdEquiv (K := ℚ) (F := F)) (StageLabels.third_pairing B)
  exact hU

private theorem second_pairing_eq (q : Triple × Triple) :
    (secondGeometry q).liftedPairing D = TensorSubspace.form pairForm D := rfl

private theorem third_pairing_eq (q : Triple × Triple) :
    (thirdGeometry q).liftedPairing StageLabels.unitForm =
      TensorSubspace.form (TensorSubspace.form pairForm D) StageLabels.unitForm := rfl

set_option maxHeartbeats 2000000 in
theorem localUpdates_nondegenerate (e : Fin n ≃ Triple) (j : Fin 3) (q : Triple × Triple) :
    ∀ p ∈ RankTrace.edges (localInput e j q) (localUpdates e j q),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate := by
  fin_cases j
  · change ∀ p ∈ RankTrace.edges (localInput e 0 q) (firstUpdates e q),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate
    rw [← first_input_map,firstUpdates]
    apply predicate_mapLabels firstMap
      (fun U : Submodule ℚ FirstAmbient => ((firstGeometry.liftedPairing pairForm).restrict U).Nondegenerate)
      (fun U : Label => (Shared50ReuseLabels.cubeForm.restrict U).Nondegenerate)
    · intro U hU
      exact LabelTransport.nondegenerate (K := ℚ) (E := FirstAmbient)
        (F := Shared50GlobalBudget.Ambient) (firstGeometry.liftedPairing pairForm) Shared50ReuseLabels.cubeForm
        (StageLabels.firstEquiv (K := ℚ) (F := Factor)) (StageLabels.first_pairing D) U hU
    · exact Shared50InvocationRank.common_nondegenerate firstGeometry rfl pairForm (vector q.1 ⊗ₜ[ℚ] vector q.2) (pair_vector_norm q.1 q.2) e
  · change ∀ p ∈ RankTrace.edges (localInput e 1 q) (secondUpdates e q),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate
    rw [← second_input_map,secondUpdates]
    apply predicate_mapLabels secondMap
      (fun U : Submodule ℚ SecondAmbient => (((secondGeometry q).liftedPairing D).restrict U).Nondegenerate)
      (fun U : Label => (Shared50ReuseLabels.cubeForm.restrict U).Nondegenerate)
    · intro U hU
      rw [second_pairing_eq] at hU
      apply LabelTransport.nondegenerate (TensorSubspace.form pairForm D) Shared50ReuseLabels.cubeForm
        StageLabels.secondEquiv (StageLabels.second_pairing D)
      exact hU
    · exact Shared50OppositeRank.common_nondegenerate (secondGeometry q) rfl D (vector q.2) (vector_norm q.2) e
  · change ∀ p ∈ RankTrace.edges (localInput e 2 q) (thirdUpdates e q),
      (Shared50ReuseLabels.cubeForm.restrict p.1).Nondegenerate ∧
      (Shared50ReuseLabels.cubeForm.restrict p.2).Nondegenerate
    rw [← third_input_map,thirdUpdates]
    apply predicate_mapLabels thirdMap
      (fun U : Submodule ℚ ThirdAmbient => (((thirdGeometry q).liftedPairing StageLabels.unitForm).restrict U).Nondegenerate)
      (fun U : Label => (Shared50ReuseLabels.cubeForm.restrict U).Nondegenerate)
    · intro U hU
      rw [third_pairing_eq] at hU
      exact third_transport D U hU
    · exact Shared50InvocationRank.common_nondegenerate (thirdGeometry q) rfl StageLabels.unitForm (1 : ℚ) (by simp [StageLabels.unitForm]) e

end
end IntegerMultBounds.Networks.Shared50GlobalTracePlacement
