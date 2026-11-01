module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFirstCachedReplicaWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRecoveryArchiveWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryLocalVolume
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

omit [NeZero s] in
theorem replicaHaloLocalSymbolVolume_le_coordinates (H : ReplicaHaloProblem s) :
    ((haloInterior s H.t H.band H.origin (H.origin+H.span)).card+8*H.span+8*(s/(H.t-s)+1))*H.wordWidth+
      6*(H.span*H.wordWidth+1) ≤ replicaHaloLocalCoordinates H*H.wordWidth := by
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  unfold replicaHaloLocalCoordinates
  nlinarith only [hw]

theorem initializedCachedReplicaInteriorWorkspace_le_coordinates (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K M cV : ℕ) (hgap : H.t-s ≤ s)
    (hl : H.l = haloInverseRingLog s H.t) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M ≤
      replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cV+
      releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H M+
      H.Fs.length*(76*(H.span*H.wordWidth)+74)+56+
      replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*(replicaHaloLocalCoordinates H*H.wordWidth) := by
  have hi := initializedReplicaHaloWorkspace_le_local (A := A) (U := U) H hQ R K cV hgap hl hV
  have hv := Nat.mul_le_mul_left (replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length)
    (replicaHaloLocalSymbolVolume_le_coordinates H)
  dsimp only [initializedCachedReplicaInteriorWorkspace,cachedReplicaInteriorFinishingWorkspace,
    initializedReplicaHaloWorkspace,initializedReplicaHaloLocalWorkspace,replicaInteriorSharedWorkspace,
    allocateZeroLineCost,realReplicaRowsCost,reverseCopyRowsCost] at hi ⊢
  nlinarith only [hi,hv]

theorem initializedCachedRecoveryWorkspace_le_coordinates (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cV : ℕ) (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    initializedCachedBatchedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K ≤
      cachedRecoverySharedWorkspace H (B.problem htarget) hQ push c M R K cV+
        (150+replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)*H.Fs.length*(replicaHaloLocalCoordinates H)*H.wordWidth := by
  let J := B.problem htarget
  obtain ⟨_,_,hwJ,hVJ⟩ := B.problem_sizing htarget
  have hnJ : J.Fs.length = H.Fs.length := B.inputs_length
  have hV' : J.metadataWidth ≤ cV*J.wordWidth := by rw [hVJ,hwJ]; exact hV
  have hi := initializedReplicaHaloWorkspace_le_local (A := A) (U := U) J hQ R K cV hgap hl hV'
  have hvol := replicaHaloLocalSymbolVolume_le_coordinates H
  have htraffic := Nat.mul_le_mul_left
    (replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length) hvol
  have hspan : H.span ≤ replicaHaloLocalCoordinates H := by unfold replicaHaloLocalCoordinates; omega
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have ht : 1 ≤ replicaHaloLocalCoordinates H := by unfold replicaHaloLocalCoordinates; omega
  have hspanw := Nat.mul_le_mul_right H.wordWidth hspan
  have hunit : 1 ≤ replicaHaloLocalCoordinates H*H.wordWidth := Nat.mul_pos ht hw
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

noncomputable def completeCachedRecoverySharedWorkspace (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cV : ℕ) : ℕ :=
  replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cV+
    (26+mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U)))*
      cachedReplicaCouplingSharedTime H+
    cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M+48*(H.span*H.wordWidth)+112+
    cachedRecoverySharedWorkspace H J hQ push c M R K cV+
    preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*cachedReplicaRecoveryHandoffSharedTime H

noncomputable def completeCachedRecoveryTrafficFactor (hQ : SS.states ≤ Q) (R cV : ℕ) : ℕ :=
  308+2*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV+
    41*preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)

/-- The actual full caller's workspace is explicit shared setup plus linear
replica storage in local coordinates, before any volume absorption. -/
theorem firstCachedReplicaRecoveryWorkspace_le_coordinates (H : ReplicaHaloProblem s)
    (target : ℕ) (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K cV : ℕ) (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t)
    (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    firstCachedReplicaRecoveryWorkspace H (B.problem htarget) hQ push c M R K ≤
      completeCachedRecoverySharedWorkspace H (B.problem htarget) hQ push c M R K cV+
      completeCachedRecoveryTrafficFactor (A := A) (U := U) hQ R cV*
        H.Fs.length*(replicaHaloLocalCoordinates H)*H.wordWidth := by
  have hf := initializedCachedReplicaInteriorWorkspace_le_coordinates (A := A) (U := U) H hQ R K M cV hgap hl hV
  have hc := releasedCachedReplicaCouplingWorkspace_shared_le (Q := Q) (A := A) (U := U) H M
  have ht := cachedReplicaCouplingTransitionWorkspace_le_preparation H hQ push c M
  have hr := initializedCachedRecoveryWorkspace_le_coordinates H target X B htarget hQ push c M R K cV hgap hl hV
  have ha := preparedRecoveryArchivesWorkspace_le_handoff (Q := Q) (A := A) (U := U) H
  have hspan : H.span ≤ replicaHaloLocalCoordinates H := by unfold replicaHaloLocalCoordinates; omega
  have hcoords : 1 ≤ replicaHaloLocalCoordinates H := by unfold replicaHaloLocalCoordinates; omega
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hline := Nat.mul_le_mul_right H.wordWidth hspan
  have hunit : 1 ≤ replicaHaloLocalCoordinates H*H.wordWidth := Nat.mul_pos hcoords hw
  have hrows : H.Fs.length*(76*(H.span*H.wordWidth)+82) ≤
      158*H.Fs.length*(replicaHaloLocalCoordinates H)*H.wordWidth := by
    have hh : 76*(H.span*H.wordWidth)+82 ≤ 158*(replicaHaloLocalCoordinates H)*H.wordWidth := by
      nlinarith only [hline,hunit]
    nlinarith only [Nat.mul_le_mul_left H.Fs.length hh]
  have harchive : preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*H.Fs.length*
      (22*(H.span*H.wordWidth)+19) ≤
      41*preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*H.Fs.length*
        (replicaHaloLocalCoordinates H)*H.wordWidth := by
    have hh : 22*(H.span*H.wordWidth)+19 ≤ 41*(replicaHaloLocalCoordinates H)*H.wordWidth := by
      nlinarith only [hline,hunit]
    nlinarith only [Nat.mul_le_mul_left
      (preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*H.Fs.length) hh]
  unfold firstCachedReplicaRecoveryWorkspace preparedCachedBatchedReplicaRecoveryWorkspace
    completeCachedRecoverySharedWorkspace completeCachedRecoveryTrafficFactor
  nlinarith only [hf,hc,ht,hr,ha,hrows,harchive]

end IntegerMultBounds.MathlibTM2.Cost
