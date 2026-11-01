module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRecoveryArchiveWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedRecoveryTotalWorkspace

/-! Complete caller space is shared core volume plus linear replica payload.
The named allowance bounds every intermediate store of the executed caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedFirstCachedReplicaRecoveryWorkspace_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := 2*cw+426009
    let C := cw*(226+80*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)+82+
      preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*(22*cw+19)
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X)
        htargetRecovery,
      firstCachedReplicaRecoveryWorkspace H (B.problem htargetRecovery) hQ push c M R K ≤
        9*Sizes.T n+C*H.Fs.length*H.t*H.p := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := 2*cw+426009
  let cVp := cV*cw
  let C := cw*(226+80*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)+82+
    preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*(22*cw+19)
  filter_upwards [selectedInitializedCachedReplicaInteriorWorkspace_le hQ push c M R K ct ce,
    selectedPreparedRecoveryArchivesWorkspace_le (Q := Q) (A := A) (U := U) cw cVp,
    selectedInitializedCachedRecoveryWorkspace_total_le hQ push c M R K ct ce] with n hf ha hr
  intro h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery
  have hfirst := hf h i H hp ht hl hu htarget hrhs
  have hrecovery := hr h i H hp ht hl hu htarget hrhs target X B htargetRecovery
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
  have hVw : H.metadataWidth ≤ cV*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw,cV] using hV
  have hVp : H.metadataWidth ≤ cVp*H.p := by
    calc
      _ ≤ cV*(cw*H.p) := hVw.trans (Nat.mul_le_mul_left cV hwH)
      _ = cVp*H.p := by dsimp only [cVp]; ring
  have harchive := ha h i H hp ht hwH (by simpa only [hp] using hu) hVp
  change _ ≤ 4*Sizes.T n+((76*cw+82)+40*cw*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t*H.p at hfirst
  change _ ≤ 4*Sizes.T n+(cw*(150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV))*H.Fs.length*H.t*H.p at hrecovery
  change _ ≤ 9*Sizes.T n+C*H.Fs.length*H.t*H.p
  dsimp only [firstCachedReplicaRecoveryWorkspace,preparedCachedBatchedReplicaRecoveryWorkspace,C]
  nlinarith only [hfirst,hrecovery,harchive]

end IntegerMultBounds.MathlibTM2.Cost
