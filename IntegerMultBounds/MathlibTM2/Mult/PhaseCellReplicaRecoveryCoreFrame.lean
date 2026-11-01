module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady

/-! Reconstruct the shared recovery core from the existing recovery exit frame.
This rule is independent of the row's field values and approximation proof. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaRecoveryCoreReady.of_recovery_frame (H : ReplicaHaloProblem s) (W : ℕ)
    {S F : Stacks 248 A} (h : ReplicaRecoveryCoreReady H W S)
    (hbank : PackedPreparedBank H.precision H.wordWidth W
      (NLogN.PhaseCellDiscreteGeometry.haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
      (embStk packedBoundaryRecoveryBase F))
    (h143 : F.R 143 = []) (h139 : F.R 139 = S.R 139)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → F.R ⟨i.val,by omega⟩ = [])
    (hretained : ∀ k ∈ packedRecoveryRetainedPorts, F.R k = S.R k)
    (hfresh : ∀ k : Fin 248, 242 ≤ k.val → F.L k = [] ∧ F.R k = [])
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), F.R k = []) :
    ReplicaRecoveryCoreReady H W F := by
  have hmaster (k : Fin 168) (hk : k ∈ couplingMasterPorts) :
      F.R (Fin.castLE (by decide) k) = S.R (Fin.castLE (by decide) k) := by
    apply hretained
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨k,?_,rfl⟩
    simp [haloRetainedHeaderPorts,hk]
  have hgeometry (k : Fin 168) (hk : k ∈ couplingIntervalPorts) :
      F.R (Fin.castLE (by decide) k) = S.R (Fin.castLE (by decide) k) := by
    apply hretained
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨k,?_,rfl⟩
    simp [haloRetainedHeaderPorts,hk]
  constructor
  · exact hbank
  · exact h143
  · intro k hk; exact (hfresh k hk).1
  · intro k hk; exact (hfresh k hk).2
  · exact h.masters.of_frame hmaster
  · rw [hretained 118 (by decide)]; exact h.stage
  · rw [hretained 120 (by decide)]; exact h.level
  · intro i h93 h110 _; exact hnative i h93 h110
  · exact hclean
  · rw [hretained 140 (by decide)]; exact h.rows
  · exact (hretained 138 (by decide)).trans h.page
  · rw [h139]; exact h.pageCount
  · exact h.geometry.of_frame (hretained 163 (by decide)) hgeometry

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
