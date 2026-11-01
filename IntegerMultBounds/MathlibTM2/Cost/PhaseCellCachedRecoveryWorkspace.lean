module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryGapFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCachedBatchedReplicaRecovery

/-! Recovery retains one preparation reserve; replicated interior storage is linear in payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def replicaInteriorSharedWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ) : ℕ :=
  3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
    ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
      (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum

noncomputable def cachedRecoverySharedWorkspace (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cV : ℕ) : ℕ :=
  initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H+
    cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M+
    replicaInteriorSharedWorkspace (A := A) (U := U) J hQ R K cV+
    2*retainedPackedPublicationMergeCost H.span H.wordWidth+56

theorem replicaHaloLocalSymbolVolume_le (H : ReplicaHaloProblem s) :
    ((haloInterior s H.t H.band H.origin (H.origin+H.span)).card+8*H.span+8*(s/(H.t-s)+1))*H.wordWidth+
      6*(H.span*H.wordWidth+1) ≤ 40*H.t*H.wordWidth := by
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hc := Nat.mul_le_mul_right H.wordWidth (replicaHaloLocalCoordinates_le H)
  unfold replicaHaloLocalCoordinates at hc
  nlinarith only [hc,hw]

theorem initializedCachedRecoveryWorkspace_le_affine (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cV : ℕ) (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K ≤
      cachedRecoverySharedWorkspace H (B.problem htarget) hQ push c M R K cV+
        (150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t*H.wordWidth := by
  let J := B.problem htarget
  obtain ⟨_,_,hwJ,hVJ⟩ := B.problem_sizing htarget
  have hnJ : J.Fs.length = H.Fs.length := B.inputs_length
  have hV' : J.metadataWidth ≤ cV*J.wordWidth := by rw [hVJ,hwJ]; exact hV
  have hi := initializedReplicaHaloWorkspace_le_local (A := A) (U := U) J hQ R K cV hgap hl hV'
  have hvol := replicaHaloLocalSymbolVolume_le H
  have htraffic := Nat.mul_le_mul_left
    (replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length) hvol
  have hspan : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hspanw := Nat.mul_le_mul_right H.wordWidth hspan
  have hunit : 1 ≤ H.t*H.wordWidth := Nat.mul_pos ht hw
  have hrows := Nat.mul_le_mul_left H.Fs.length hspanw
  have hcount := Nat.mul_le_mul_left H.Fs.length hunit
  unfold initializedReplicaHaloWorkspace initializedReplicaHaloLocalWorkspace at hi
  change _ ≤ _ at hi
  rw [hnJ,hwJ] at hi
  unfold initializedCachedBatchedReplicaRecoveryWorkspace cachedBatchedReplicaRecoveryWorkspace
    cachedRecoverySharedWorkspace replicaRecoveryInteriorWorkspace replicaInteriorSharedWorkspace
  change _ ≤ _
  rw [hnJ,hwJ]
  simp only [reverseCopyRowsCost,allocateZeroLineCost,realReplicaRowsCost] at hi ⊢
  dsimp only [J] at hi
  have hsJ : (B.problem htarget).span = H.span := rfl
  have htJ : (B.problem htarget).t = H.t := rfl
  have hbJ : (B.problem htarget).band = H.band := rfl
  have hoJ : (B.problem htarget).origin = H.origin := rfl
  simp only [hsJ,htJ,hbJ,hoJ] at hi ⊢
  nlinarith only [hi,htraffic,hrows,hcount]

/-- Reprice the existing executed caller trace using its shared reserve and payload stock. -/
theorem initializedCachedRecovery_within_affine {P : Type} {body : P → Pr P 392 Q A U}
    (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) htarget (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K cV : ℕ)
    {depth steps : ℕ} {z z' : Store (HΓ (T := 392) A) (HS 392 Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K)
      depth (initializedCachedBatchedReplicaRecovery hR hQ) z steps z')
    (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      (cachedRecoverySharedWorkspace H (B.problem htarget) hQ push c M R K cV+
        (150+40*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*H.t*H.wordWidth))
      depth (initializedCachedBatchedReplicaRecovery hR hQ) z steps z' := by
  have hc := initializedCachedRecoveryWorkspace_le_affine H target X B htarget hQ push c M R K cV hgap hl hV
  apply he.mono
  intro d state hs
  exact hs.trans (Nat.add_le_add_left hc _)

end IntegerMultBounds.MathlibTM2.Cost
