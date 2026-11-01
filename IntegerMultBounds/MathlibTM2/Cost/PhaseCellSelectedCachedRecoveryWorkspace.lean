module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! Selected recovery stores replica payload linearly, with one shared scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedInitializedCachedRecoveryWorkspace_le_affine (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct ce : ℕ)
    {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (H : ReplicaHaloProblem (Sizes.s n i)) (hp : H.p = Sizes.p n) (ht : H.t = Sizes.t n i)
    (hl : H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (hu : H.u ≤ Sizes.p n) (htarget : H.target ≤ ct*Sizes.p n) (hrhs : H.rhsExp ≤ ce*Sizes.p n)
    (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X) htargetRecovery :
    let cw := 16*20+8*ct+8*ce+128
    let cV := 2*cw+426009
    initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htargetRecovery) hQ push c M R K ≤
      cachedRecoverySharedWorkspace H (B.problem htargetRecovery) hQ push c M R K cV+
        (cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := 2*cw+426009
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
  have hVw : H.metadataWidth ≤ cV*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
      ReplicaHaloProblem.wordWidth,hp,ht,hl,cw,cV] using hV
  have hg : H.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
  have hlRing : H.l = haloInverseRingLog (Sizes.s n i) H.t := by rw [ht]; exact hl
  have hc := initializedCachedRecoveryWorkspace_le_affine H target X B htargetRecovery hQ push
    c M R K cV hg hlRing hVw
  have hs := Nat.mul_le_mul_left
    ((150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t) hwH
  change initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htargetRecovery) hQ push c M R K ≤
    cachedRecoverySharedWorkspace H (B.problem htargetRecovery) hQ push c M R K cV+
      (cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p
  nlinarith only [hc,hs]

end IntegerMultBounds.MathlibTM2.Cost
