module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedCyclicRecoveryLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! Pay the shared part of the actual cyclic recovery bill once per scheduled
core. Replica work remains explicit; no execution multiplicity is assumed away. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellMatrix

private theorem boundaryMaskCost_le_recovery {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    placedReplicaBoundaryMaskCost H ≤
      initializeRecoveryMasksCost H.metadataWidth H.span H.band := by
  unfold placedReplicaBoundaryMaskCost initializeRecoveryMasksCost
  nlinarith only [Nat.zero_le (H.span*tblC H.metadataWidth 1),
    Nat.zero_le (H.band*tblC H.metadataWidth 1)]

theorem solvedCyclicRecoverySharedTime_core_le {s : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (cV t p : ℕ) (hst : s ≤ t)
    (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hH : H.metadataWidth ≤ cV*p) (hK : K.metadataWidth ≤ cV*p) :
    solvedCyclicRecoverySharedTime H K ≤ 120024*(cV+5)^2*(t^6*p^4) := by
  have hHN : H.span ≤ t := by have := H.span_fit; omega
  have hKN : K.span ≤ t := by have := K.span_fit; omega
  have hHM := initializeRecoveryMasksCost_core_le cV hHN (H.band_fit.trans hst) ht hp hH
  have hKM := initializeRecoveryMasksCost_core_le cV hKN (K.band_fit.trans hst) ht hp hK
  have hHB := boundaryMaskCost_le_recovery H
  have hKB := boundaryMaskCost_le_recovery K
  have hpos : 1 ≤ (cV+5)^2*(t^6*p^4) := by
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold solvedCyclicRecoverySharedTime
  simp only [ReplicaHaloProblem.band] at hHB hKB ⊢
  nlinarith only [hHM,hKM,hHB,hKB,hpos]

/-- A bounded actual call list pays shared recovery once per entry. Repeated
cores count repeatedly; the caller must prove this bound for its real list. -/
theorem selectedCyclicRecoverySharedSchedule_volume_le (cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (jobs : List ι)
      (H K : ι → ReplicaHaloProblem (Sizes.s n i)),
      jobs.length ≤ 2*Sizes.t n i →
      (∀ j ∈ jobs, (H j).metadataWidth ≤ cV*Sizes.p n ∧
        (K j).metadataWidth ≤ cV*Sizes.p n) →
      scale*(jobs.map (fun j => solvedCyclicRecoverySharedTime (H j) (K j))).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (120024*(cV+5)^2) 4 6 scale] with n hs
  intro ι h i _ jobs H K hcount hwidth
  apply hs i jobs _ hcount
  intro j hj
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  simpa only [Nat.mul_assoc] using solvedCyclicRecoverySharedTime_core_le (H j) (K j) cV _ _
    (h.good.lt i).le ht hp (hwidth j hj).1 (hwidth j hj).2

/-- The actual complete recovery bill reduces to one setup-volume allowance
and the sum of per-replica charges. This is a time ledger, not a space claim. -/
theorem selectedCyclicRecoverySchedule_time_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (jobs : List ι)
      (H K : ι → ReplicaHaloProblem (Sizes.s n i)) (replicas N span w : ι → ℕ),
      jobs.length ≤ 2*Sizes.t n i →
      (∀ j ∈ jobs, (H j).metadataWidth ≤ cV*Sizes.p n ∧
        (K j).metadataWidth ≤ cV*Sizes.p n) →
      (∀ j ∈ jobs, (H j).Fs.length = replicas j) →
      (∀ j ∈ jobs, (K j).Fs.length = replicas j) →
      (jobs.map (fun j => solvedCyclicRecoveryCost (H j) (K j)
        (replicas j) (N j) (span j) (w j))).sum ≤ Sizes.T n+
        (jobs.map (fun j => replicas j*solvedCyclicRecoveryReplicaTime
          (H j) (K j) (N j) (span j) (w j))).sum := by
  filter_upwards [selectedCyclicRecoverySharedSchedule_volume_le cV 1] with n hs
  intro ι h i _ jobs H K replicas N span w hcount hwidth hH hK
  rw [solvedCyclicRecoveryCost_sum jobs H K replicas N span w hH hK]
  exact Nat.add_le_add_right (by simpa only [one_mul] using hs h i jobs H K hcount hwidth) _

/-- The computed equal-length core class discharges the call-count premise.
This prices one traversal; repeated class traversals still require their own ledger. -/
theorem selectedCyclicCoreClassRecovery_time_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (width radius L : ℕ), 0 < width →
      ∀ (H K : ℕ → ReplicaHaloProblem (Sizes.s n i)) (replicas N span w : ℕ → ℕ),
      let jobs := coreGatherIndices (Sizes.s n i) width radius L
      (∀ j ∈ jobs, (H j).metadataWidth ≤ cV*Sizes.p n ∧
        (K j).metadataWidth ≤ cV*Sizes.p n) →
      (∀ j ∈ jobs, (H j).Fs.length = replicas j) →
      (∀ j ∈ jobs, (K j).Fs.length = replicas j) →
      (jobs.map (fun j => solvedCyclicRecoveryCost (H j) (K j)
        (replicas j) (N j) (span j) (w j))).sum ≤ Sizes.T n+
        (jobs.map (fun j => replicas j*solvedCyclicRecoveryReplicaTime
          (H j) (K j) (N j) (span j) (w j))).sum := by
  filter_upwards [selectedCyclicRecoverySchedule_time_le cV] with n hs
  intro h i _ width radius L hw H K replicas N span w
  apply hs h i _ H K replicas N span w
  have hc := coreGatherIndices_length_le (Sizes.s n i) width radius L hw
  have ht := h.good.lt i
  omega

end IntegerMultBounds.MathlibTM2.Cost
