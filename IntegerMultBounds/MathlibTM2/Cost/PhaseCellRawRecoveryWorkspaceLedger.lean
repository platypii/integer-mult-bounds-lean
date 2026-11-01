module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCompleteCachedRecoveryLocalWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryInputStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputLedger

/-! Keep raw caller setup explicit and all replica workspace linear in local
volume before summing cleanup or taking a schedule's peak scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def rawRecoveryJobSharedWorkspace (r : RawRecoveryJob s)
    (B : ReplicaRecoveryBatch r.problem r.target r.solution)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K cV : ℕ) : ℕ :=
  2*rawRecoveryJobSharedInputStock r+
    normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*normalizeRecoveryInputSharedTime r.problem r.W+
    generatedReplicaBoundaryFactoryPush (A := A) (U := U) hR hQ*
      generatedReplicaBoundaryFactoryCost r.problem r.target+
    completeCachedRecoverySharedWorkspace r.problem (B.problem r.sizing) hQ push c M R K cV

noncomputable def rawRecoveryJobRowWorkspace (r : RawRecoveryJob s) (hQ : SS.states ≤ Q)
    (R cV : ℕ) : ℕ :=
  2*rawRecoveryJobRowInputStock r+
    normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*normalizeRecoveryInputRowTime r.problem r.W+
    completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV*
      (replicaHaloLocalCoordinates r.problem)*r.problem.wordWidth

theorem rawRecoveryJob_runStock_le_affine (r : RawRecoveryJob s)
    (B : ReplicaRecoveryBatch r.problem r.target r.solution)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K cV : ℕ)
    (hgap : r.problem.t-s ≤ s) (hl : r.problem.l = haloInverseRingLog s r.problem.t)
    (hV : r.problem.metadataWidth ≤ cV*r.problem.wordWidth) :
    r.runStock hR hQ push c M R K B ≤ rawRecoveryJobSharedWorkspace r B hR hQ push c M R K cV+
      r.problem.Fs.length*rawRecoveryJobRowWorkspace (A := A) (U := U) r hQ R cV := by
  have hi := rawRecoveryJob_initialStock_le (A := A) r
  have hg : generatedRecoveryInputStock r.problem [] [] ≤ rawRecoveryJobInputStock r := by
    unfold rawRecoveryJobInputStock
    omega
  have hf := firstCachedReplicaRecoveryWorkspace_le_coordinates r.problem r.target r.solution B r.sizing
    hQ push c M R K cV hgap hl hV
  have hN : r.problem.Fs.length = r.inputFields.length := by
    simpa only [recoveryInputFields,List.length_map] using congrArg List.length r.fields
  rw [rawRecoveryJobInputStock_affine] at hi hg
  unfold RawRecoveryJob.runStock RawRecoveryJob.inputTime generatedFirstCachedReplicaRecoveryWorkspace
    rawRecoveryJobSharedWorkspace rawRecoveryJobRowWorkspace
  rw [normalizeRecoveryInputCost_affine,←hN]
  nlinarith only [hi,hg,hf]

/-- The repeated workspace has exponent one in precision; the fast-time
p^(129/128) factor never enters the space bound. -/
theorem rawRecoveryJobRowWorkspace_coordinates_le (r : RawRecoveryJob s) (hQ : SS.states ≤ Q)
    (R cV cw cW : ℕ) (hw : r.problem.wordWidth ≤ cw*r.problem.p) (hW : r.W ≤ cW*r.problem.p) :
    rawRecoveryJobRowWorkspace (A := A) (U := U) r hQ R cV ≤
      (2*(392+cw+cW)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*(4*cW+12*cw+28)+
        completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV*cw)*
          replicaHaloLocalCoordinates r.problem*r.problem.p := by
  let H := r.problem
  let V := replicaHaloLocalCoordinates H
  have hspan : H.span ≤ V := by unfold V replicaHaloLocalCoordinates; omega
  have hvolume : 1 ≤ V := by unfold V replicaHaloLocalCoordinates; omega
  have hunit : 1 ≤ V*H.p := Nat.mul_pos hvolume H.p_pos
  have hspanp := Nat.mul_le_mul_right H.p hspan
  have hi := rawRecoveryJobRowInputStock_le r cw cW hw hW
  have hinput : rawRecoveryJobRowInputStock r ≤ (392+cw+cW)*V*H.p := by
    nlinarith only [hi,hunit,Nat.mul_le_mul_left (cw+cW) hspanp]
  have hn := normalizeRecoveryInputRowTime_le H r.W cw cW hw hW
  have hnorm : normalizeRecoveryInputRowTime H r.W ≤ (4*cW+12*cw+28)*V*H.p := by
    nlinarith only [hn,Nat.mul_le_mul_left (4*cW+12*cw+28) hspanp]
  have hcoords : replicaHaloLocalCoordinates H ≤ V := le_refl _
  have hc : replicaHaloLocalCoordinates H*H.wordWidth ≤ cw*V*H.p := by
    nlinarith only [Nat.mul_le_mul hcoords hw]
  have hnorm' := Nat.mul_le_mul_left (normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)) hnorm
  have hc' := Nat.mul_le_mul_left (completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV) hc
  unfold rawRecoveryJobRowWorkspace
  change _ ≤ (2*(392+cw+cW)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*(4*cW+12*cw+28)+
    completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV*cw)*V*H.p
  nlinarith only [hinput,hnorm',hc']

theorem rawRecoveryJobRowWorkspace_local_le (r : RawRecoveryJob s) (hQ : SS.states ≤ Q)
    (R cV cw cW : ℕ) (hw : r.problem.wordWidth ≤ cw*r.problem.p) (hW : r.W ≤ cW*r.problem.p) :
    rawRecoveryJobRowWorkspace (A := A) (U := U) r hQ R cV ≤
      (2*(392+cw+cW)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*(4*cW+12*cw+28)+
        completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV*cw)*
          replicaRecoveryLocalVolume r.problem*r.problem.p := by
  have hc : replicaHaloLocalCoordinates r.problem ≤ replicaRecoveryLocalVolume r.problem := by
    unfold replicaRecoveryLocalVolume
    omega
  apply (rawRecoveryJobRowWorkspace_coordinates_le r hQ R cV cw cW hw hW).trans
  exact Nat.mul_le_mul_right r.problem.p (Nat.mul_le_mul_left _ hc)

end IntegerMultBounds.MathlibTM2.Cost
