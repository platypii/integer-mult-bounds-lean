module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedCouplingLocalFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedCyclicRecoveryLedger

/-! The executed cyclic recovery row uses the boundary-masked instance of the
existing cached local coupling. Transfer its local-volume bound directly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem cachedRecoveryCouplingRowCost_eq_local (H : ReplicaHaloProblem s) :
    cachedRecoveryCouplingRowCost H =
      cachedReplicaLocalCouplingCost true (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span H.metadataWidth := by
  rfl

theorem cachedRecoveryCouplingRowCost_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      (cachedRecoveryCouplingRowCost H : ℝ) ≤
        D*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hrow⟩ := cachedReplicaLocalCoupling_local_fast_le cw cV
  refine ⟨D,hD,?_⟩
  intro s _ H hw hV
  rw [cachedRecoveryCouplingRowCost_eq_local]
  exact hrow H hw hV true

theorem cyclicRecoveryNativeTraffic_le (N n w : ℕ) :
    nativeCyclicBoundaryRowCost N n w+28*(n*w)+76 ≤
      300*(N+n+1)*(w+1) := by
  have h := residualBatchRecoveryInputCost_le N w
  unfold nativeCyclicBoundaryRowCost retireCountedLineCost
  nlinarith only [h]

/-- Both numerical couplings use their local volumes. Projection, retirement
and archive traffic are linear in boundary plus window volume. -/
theorem solvedCyclicRecoveryReplicaTime_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
      (N n w : ℕ), H.wordWidth = w → K.wordWidth = w → H.span+K.span ≤ n →
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      K.wordWidth ≤ cw*K.p → K.metadataWidth ≤ cV*K.p →
      (solvedCyclicRecoveryReplicaTime H K N n w : ℝ) ≤
        D*((replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ)+
            (replicaRecoveryLocalVolume K : ℝ)*(K.p : ℝ)^(129/128 : ℝ))+
          300*((N+n+1 : ℕ) : ℝ)*(w+1) := by
  obtain ⟨D,hD,hrow⟩ := cachedRecoveryCouplingRowCost_local_fast_le cw cV
  refine ⟨D,hD,?_⟩
  intro s _ H K N n w hHW hKW hspan hwH hVH hwK hVK
  have hH := hrow H hwH hVH
  have hK := hrow K hwK hVK
  have hb := (Nat.cast_le (α := ℝ)).mpr
    (solvedCyclicRecoveryReplicaTime_le_window H K N n w hHW hKW hspan)
  have hn := (Nat.cast_le (α := ℝ)).mpr (cyclicRecoveryNativeTraffic_le N n w)
  push_cast at hb hn ⊢
  nlinarith only [hb,hH,hK,hn]

/-- Apply the fast ledger to the actual step allowance returned by recovery.
The execution and its output certificates need no new witness or hypothesis. -/
theorem solvedCyclicRecovery_steps_local_fast_le (cw cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
      (replicas N n w : ℕ), H.Fs.length = replicas → K.Fs.length = replicas →
      H.wordWidth = w → K.wordWidth = w → H.span+K.span ≤ n →
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      K.wordWidth ≤ cw*K.p → K.metadataWidth ≤ cV*K.p →
      ∀ steps : ℕ, steps ≤ solvedCyclicRecoveryCost H K replicas N n w →
      (steps : ℝ) ≤ (solvedCyclicRecoverySharedTime H K : ℝ)+
        replicas*(D*((replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ)+
          (replicaRecoveryLocalVolume K : ℝ)*(K.p : ℝ)^(129/128 : ℝ))+
          300*((N+n+1 : ℕ) : ℝ)*(w+1)) := by
  obtain ⟨D,hD,hfast⟩ := solvedCyclicRecoveryReplicaTime_local_fast_le cw cV
  refine ⟨D,hD,?_⟩
  intro s _ H K replicas N n w hH hK hHW hKW hspan hwH hVH hwK hVK steps hsteps
  have hr := hfast H K N n w hHW hKW hspan hwH hVH hwK hVK
  rw [solvedCyclicRecoveryCost_eq_shared_add_replicas H K replicas N n w hH hK] at hsteps
  have hs := (Nat.cast_le (α := ℝ)).mpr hsteps
  push_cast at hs
  exact hs.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg replicas)))

end IntegerMultBounds.MathlibTM2.Cost
