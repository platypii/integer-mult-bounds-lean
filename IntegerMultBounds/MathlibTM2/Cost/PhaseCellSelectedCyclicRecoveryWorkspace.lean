module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedPreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryMaskInitialization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryPushBounds

/-! Cyclic recovery reuses the retained recovery worker's selected shared bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def cyclicRecoveryMulPush (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr)

theorem cachedRecoveryCouplingWorkspace_le_preparation (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ) :
    cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ ≤
      cachedReplicaRecoveryPreparationRowWorkspace H hQ push c (cyclicRecoveryMulPush (A := A) (U := U) hQ) := by
  unfold cachedRecoveryCouplingWorkspace cachedReplicaRecoveryPreparationRowWorkspace
    cachedCollectedReplicaRecoveryRhsWorkspace cachedPackedBoundaryRecoveryRhsWorkspace
    cachedPreparedSharedLocalFeedCouplingWorkspace cyclicRecoveryMulPush
  dsimp only
  omega

theorem selectedCachedRecoveryCouplingWorkspace_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      scale*cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ ≤ Sizes.T n := by
  filter_upwards [selectedCachedRecoveryPreparationWorkspace_volume_le hQ push 0
    (cyclicRecoveryMulPush (A := A) (U := U) hQ) cw cV scale] with n hs
  intro h i _ H hp ht hw hV
  exact (Nat.mul_le_mul_left scale (cachedRecoveryCouplingWorkspace_le_preparation H hQ push 0)).trans
    (hs h i H hp ht hw hV)

end IntegerMultBounds.MathlibTM2.Cost
