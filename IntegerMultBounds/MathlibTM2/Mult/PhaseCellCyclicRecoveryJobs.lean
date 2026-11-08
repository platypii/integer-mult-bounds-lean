module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPlacement

/-! The two retained recovery jobs keep their existing physical banks. Their
ownership remains disjoint after extending the caller to 840 tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

theorem CachedReplicaPassPlacement.reindex_owns_source {T T' : ℕ}
    (job : CachedReplicaPassPlacement T) (e : Fin T → Fin T') (he : Function.Injective e)
    {k : Fin T'} (h : (job.reindex e he).Owns k) : ∃ i, job.Owns i ∧ e i = k := by
  cases h with
  | bank i => exact ⟨job.coupling.bank i,.bank i,by simp [CachedReplicaPassPlacement.reindex]⟩
  | gather i => exact ⟨job.plan.gather i,.gather i,rfl⟩
  | solver i => exact ⟨job.plan.solver i,.solver i,rfl⟩
  | output => exact ⟨job.output,.output,rfl⟩
  | rhs => exact ⟨job.rhs,.rhs,rfl⟩

namespace CyclicRecoveryPlacement

def leftJob : CachedReplicaPassPlacement 840 :=
  CyclicReplicaPlacement.left.reindex extend (Fin.castLE_injective _)

def rightJob : CachedReplicaPassPlacement 840 :=
  CyclicReplicaPlacement.right.reindex extend (Fin.castLE_injective _)

theorem jobs_disjoint (k : Fin 840) (hl : leftJob.Owns k) : ¬rightJob.Owns k := by
  intro hr
  obtain ⟨i,hi,hei⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hl
  obtain ⟨j,hj,hej⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hr
  have hij : i = j := Fin.castLE_injective _ (hei.trans hej.symm)
  subst j
  exact CyclicReplicaPlacement.disjoint i hi hj

theorem native_left_disjoint (i : Fin 240) (k : Fin 840) (hk : leftJob.Owns k) : k ≠ bank i := by
  obtain ⟨j,hj,hej⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hk
  rw [← hej]
  exact (bank_left_disjoint i j hj).symm

theorem native_right_disjoint (i : Fin 240) (k : Fin 840) (hk : rightJob.Owns k) : k ≠ bank i := by
  obtain ⟨j,hj,hej⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hk
  rw [← hej]
  exact (bank_right_disjoint i j hj).symm

theorem source_left_disjoint (k : Fin 840) (hk : leftJob.Owns k) : k ≠ bank 132 := by
  obtain ⟨i,hi,hei⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hk
  rw [← hei]
  exact (bank_left_disjoint 132 i hi).symm

theorem source_right_disjoint (k : Fin 840) (hk : rightJob.Owns k) : k ≠ bank 132 := by
  obtain ⟨i,hi,hei⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hk
  rw [← hei]
  exact (bank_right_disjoint 132 i hi).symm

end CyclicRecoveryPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
