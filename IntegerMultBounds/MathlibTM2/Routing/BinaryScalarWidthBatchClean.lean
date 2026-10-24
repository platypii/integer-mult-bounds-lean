module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidthBatch
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Restore an exact-width control bank and price cleanup structurally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T A : ℕ} {J : Type}

theorem binaryScalarWidthBatchBank_clean (R : Fin T → List (Fin (A + 4)))
    (rg : J → Fin 6 → Fin T) (L x : J → ℕ) (jobs : List J)
    (hblank : ∀ j ∈ jobs, R (rg j 2) = []) :
    metadataCleared (binaryScalarWidthBatchBank R rg L x jobs) (jobs.map (fun j => rg j 2)) = R := by
  funext k
  by_cases hk : k ∈ jobs.map (fun j => rg j 2)
  · rw [metadataCleared_at _ _ _ hk]
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    exact (hblank j hj).symm
  · rw [metadataCleared_keep _ _ _ hk,binaryScalarWidthBatchBank_keep R rg L x jobs k hk]

theorem binaryScalarWidthBatchBank_cleanCost_le (R : Fin T → List (Fin (A + 4)))
    (rg : J → Fin 6 → Fin T) (L x : J → ℕ) (jobs : List J)
    (hdst : (jobs.map (fun j => rg j 2)).Nodup) (B : ℕ) (hL : ∀ j ∈ jobs, L j ≤ B) :
    metadataCleanCost (binaryScalarWidthBatchBank R rg L x jobs) (jobs.map (fun j => rg j 2)) ≤
      jobs.length * (2 * B + 2) + 1 := by
  have hc := metadataCleanCost_le (binaryScalarWidthBatchBank R rg L x jobs)
    (jobs.map (fun j => rg j 2)) B (by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
      rw [binaryScalarWidthBatchBank_at R rg L x jobs hdst j hj]
      simpa only [IntegerMultBounds.MathlibTM2.Host.length_binSyms] using hL j hj)
  simpa only [List.length_map] using hc

end IntegerMultBounds.MathlibTM2.Routing
