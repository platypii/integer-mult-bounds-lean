module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedCouplingWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedRecoveryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaRecoveryPreparationRow

/-! One physical envelope bounds the complete recovery-preparation scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def recoveryPreparationPushCoefficients (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M : ℕ) : List ℕ :=
  [c,M,push.normalize,push.unscale,push.reciprocal,push.column,
      mnProgPush (packedBoundaryRecoveryInputs (P := Empty) (Q := Q) (A := A) (U := U)),
      mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159),
      mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U)),
      mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))]

theorem cachedRecoveryPreparationWorkspace_poly (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M Z : ℕ) (hZ : 1 ≤ Z)
    (hdim : ∀ x ∈ [H.precision,H.wordWidth,H.span,H.metadataWidth,12*H.band+1,
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card,
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length], x ≤ Z)
    (hpush : ∀ x ∈ recoveryPreparationPushCoefficients hQ push c M, x ≤ Z) :
    cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ 1000000*(ssMulConst+1)*Z^4 := by
  have hq := hdim H.precision (by simp)
  have hw := hdim H.wordWidth (by simp)
  have hN := hdim H.span (by simp)
  have hV := hdim H.metadataWidth (by simp)
  have hW := hdim (12*H.band+1) (by simp)
  have hn := hdim (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (by simp)
  have hp : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hband : H.band ≤ Z := by omega
  have hrows : 2*H.band+1 ≤ Z := by omega
  have hcoupling := cachedPreparedSharedLocalFeedCouplingWorkspace_poly (Q := Q) (A := A) (U := U)
    (P := 2^15*H.p) (s := s) (t := H.t) (u := H.u) (a := H.origin)
    (b := H.origin+H.span) (origin := H.origin) hZ (hpush M (by simp [recoveryPreparationPushCoefficients])) hq hw hp
    hN hV hband hrows (hdim _ (by simp))
    (hpush _ (by simp [recoveryPreparationPushCoefficients])) (hpush _ (by simp [recoveryPreparationPushCoefficients])) (hpush _ (by simp [recoveryPreparationPushCoefficients]))
  have hnum := preparedResidualSolveWorkspace_poly hZ (hpush push.normalize (by simp [recoveryPreparationPushCoefficients])) (hpush push.unscale (by simp [recoveryPreparationPushCoefficients]))
    (hpush push.reciprocal (by simp [recoveryPreparationPushCoefficients])) (hpush push.column (by simp [recoveryPreparationPushCoefficients])) hq hw hn hW
  have hinput := packedBoundaryRecoveryInputsCost_poly hZ hZ hV hN hn hw
  have hinput' := Nat.mul_le_mul (hpush
    (mnProgPush (packedBoundaryRecoveryInputs (P := Empty) (Q := Q) (A := A) (U := U))) (by simp [recoveryPreparationPushCoefficients])) hinput
  have hstage : replicaRecoveryInputsCost H ≤ 14*(Z*Z)+4*Z+6*Z+24 := by
    unfold replicaRecoveryInputsCost
    gcongr
  have hboundary : c*replicaBoundaryRhsCost H ≤
      Z*((12*(Z*Z)+12+(Z*(16*Z+10)+16))+60*(Z+1)*Z+60*Z+60+6*(Z*Z)+6) := by
    unfold replicaBoundaryRhsCost stageReplicaBoundaryRhsCost
    dsimp only
    gcongr
    exact hpush c (by simp [recoveryPreparationPushCoefficients])
  have hcollect : 2*(18*(H.span*H.wordWidth)+18) ≤ 2*(18*(Z*Z)+18) := by gcongr
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hs : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  unfold cachedReplicaRecoveryPreparationRowWorkspace BoundarySolvePushBounds.workspace
    cachedCollectedReplicaRecoveryRhsWorkspace cachedPackedBoundaryRecoveryRhsWorkspace
  nlinarith only [hcoupling,hnum,hinput',hstage,hboundary,hcollect,h3,h2,h1,h0,hs]

theorem cachedRecoveryPreparationWorkspace_envelope_le (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M Y : ℕ) (hY : 1 ≤ Y)
    (hdim : ∀ x ∈ [H.precision,H.wordWidth,H.span,H.metadataWidth,H.band,
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card], x ≤ Y)
    (hpush : ∀ x ∈ recoveryPreparationPushCoefficients hQ push c M, x ≤ Y) :
    cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ (1000000*(ssMulConst+1)*16^4)*Y^8 := by
  have hY2 : Y ≤ Y^2 := Nat.le_self_pow (by decide) Y
  have hYZ : Y ≤ 16*Y^2 := by omega
  have hZ : 1 ≤ 16*Y^2 := hY.trans hYZ
  have hspan := hdim H.span (by simp)
  have hband := hdim H.band (by simp)
  have hpage := couplingCoefficientPageInterval_length_le (2^15*H.p) H.precision s H.t H.u H.band
    H.origin (H.origin+H.span) H.origin H.span
  have hlength : (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span).length ≤ 16*Y^2 := by
    have hm := Nat.mul_le_mul hspan (show 2*H.band+1 ≤ 2*Y+1 by omega)
    nlinarith only [hpage,hm,hY2]
  have hc := cachedRecoveryPreparationWorkspace_poly H hQ push c M (16*Y^2) hZ (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hdim _ (by simp)).trans hYZ
    · exact (hdim _ (by simp)).trans hYZ
    · exact hspan.trans hYZ
    · exact (hdim _ (by simp)).trans hYZ
    · nlinarith only [hband,hY,hY2]
    · exact (hdim _ (by simp)).trans hYZ
    · exact hlength) (fun x hx => (hpush x hx).trans hYZ)
  have heq : (16*Y^2)^4 = 16^4*Y^8 := by ring
  rw [heq] at hc
  simpa only [Nat.mul_assoc] using hc

end IntegerMultBounds.MathlibTM2.Cost
