module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryArchivesStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryHandoff

/-! Archive preparation reuses shared handoff absorption and adds linear
replica payload. Its fixed program push bound stays symbolic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem preparedRecoveryArchivesWorkspace_le_handoff {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    preparedReplicaRecoveryArchivesWorkspace (Q := Q) (A := A) (U := U) H ≤
      preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*cachedReplicaRecoveryHandoffSharedTime H+
        preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*H.Fs.length*(22*(H.span*H.wordWidth)+19) := by
  unfold preparedReplicaRecoveryArchivesWorkspace copyRowsOrderedCost cachedReplicaRecoveryHandoffSharedTime
  nlinarith only [Nat.zero_le (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*
    replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span))]

theorem selectedPreparedRecoveryArchivesWorkspace_le (cw cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.u ≤ H.p → H.metadataWidth ≤ cV*H.p →
      preparedReplicaRecoveryArchivesWorkspace (Q := Q) (A := A) (U := U) H ≤
        Sizes.T n+(preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*(22*cw+19))*H.Fs.length*H.t*H.p := by
  let C := preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedCachedReplicaCouplingSharedTime_volume_le cw cV (100*C)] with n hs
  intro h i _ H hp ht hw hu hV
  have hshared := hs h i H hp ht hw hu hV
  have hhand := Nat.mul_le_mul_left C (cachedReplicaRecoveryHandoffSharedTime_le H)
  have ht1 : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hp1 : 1 ≤ H.p := H.p_pos
  have hspan : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hline := Nat.mul_le_mul hspan hw
  have hunit : 1 ≤ H.t*H.p := Nat.mul_pos ht1 hp1
  have hrow : 22*(H.span*H.wordWidth)+19 ≤ (22*cw+19)*H.t*H.p := by nlinarith only [hline,hunit]
  have hrows := Nat.mul_le_mul_left (C*H.Fs.length) hrow
  have hbudget := preparedRecoveryArchivesWorkspace_le_handoff (Q := Q) (A := A) (U := U) H
  change _ ≤ Sizes.T n+(C*(22*cw+19))*H.Fs.length*H.t*H.p
  change _ ≤ C*cachedReplicaRecoveryHandoffSharedTime H+C*H.Fs.length*(22*(H.span*H.wordWidth)+19) at hbudget
  nlinarith only [hshared,hhand,hrows,hbudget]

end IntegerMultBounds.MathlibTM2.Cost
