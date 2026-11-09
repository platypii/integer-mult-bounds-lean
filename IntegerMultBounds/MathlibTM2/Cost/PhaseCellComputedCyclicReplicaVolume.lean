module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicEmptyRecoveryVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems

/-! Instantiate computed fitting-class volume with the actual cyclic replica
constructors. Numerical data, solutions and proof fields are never compared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem computedCyclicReplicaProblems_localVolume_sum_le
    {s t p u l : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d)
    (target rhsExp width depth L : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hguard : depth*PhaseCellBand.width p u ≤ width)
    (hcell : s/(t-s)+1 ≤ width)
    (hprepare : p^2+(PhaseCellBand.width p u)^2 ≤ width)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ k,
      ‖value (executionPrecision p l target rhsExp) (F k)‖ ≤ (2 : ℝ)^rhsExp)
    (H K : ℕ → ReplicaHaloProblem s)
    (hactual : ∀ k ∈ coreGatherIndices s width (depth*PhaseCellBand.width p u) L,
      ∃ (ha : coreStart width k-depth*PhaseCellBand.width p u < s) (hn : L ≤ s),
        H k = axis.cyclicLeftReplicaProblem target rhsExp
          (coreStart width k-depth*PhaseCellBand.width p u) L ha Fs hF ∧
        K k = axis.cyclicRightReplicaProblem target rhsExp
          (coreStart width k-depth*PhaseCellBand.width p u) L hn Fs hF) :
    ((coreGatherIndices s width (depth*PhaseCellBand.width p u) L).map (fun k =>
      replicaRecoveryLocalVolume (H k)+replicaRecoveryLocalVolume (K k))).sum ≤
      680*(s+(t-s)*(PhaseCellBand.width p u)^2) := by
  apply computedFittingCyclicRecoveryLocalVolume_sum_le axis.hst p width
    (PhaseCellBand.width p u) depth L hw hwidth hguard
    (PhaseCellBand.width_pos p u) hcell hprepare H K
  intro k hk
  obtain ⟨ha,hn,hH,hK⟩ := hactual k hk
  rw [hH,hK]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end IntegerMultBounds.MathlibTM2.Cost
