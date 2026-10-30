module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyNormalizedBatch

/-! Workspace accounting separates the one shared numerical scratch bank from
linear input, archive and normalization storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The shared workspace allowance already pays the zero-replica numerical
execution, including factor construction and publication controls. -/
theorem packedKeyNormalizedBatchCost_zero_le_workspace
    (B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius : ℕ)
    [NeZero s] :
    packedKeyNormalizedBatchCost B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0 ≤
      packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0 := by
  simp only [packedKeyNormalizedBatchCost,packedKeyNormalizedWorkspace,packedKeyComplexWorkspace,
    packedKeyRealBatchCost,packedHaloBatchCostFromSetup,packedHaloGeometryWorkspace,
    packedHaloBatchCost,packedCoreBatchPublicationCost,packedCoreArchiveControlsCost,executionWidth,
    Nat.mul_add,Nat.add_mul,Nat.zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
  nlinarith

theorem packedHaloGeometryWorkspace_affine
    (p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N : ℕ) [NeZero s] :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N =
      packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        N*(4+100*((coreLength s coreWidth k+2*radius)*w+1)) := by
  simp only [packedHaloGeometryWorkspace]
  ring

/-- The replica-dependent workspace contains only linear data processing.
Factor construction, numerical solves and their scratch are absent. -/
noncomputable def packedKeyWorkspaceReplicaCost
    (p q W u l s t a b boundaryTarget rhsExp targetOut coreWidth k radius : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E := inverseExecutionExponent p l targetOut B.card band
  let L := coreLength s coreWidth k
  26*((b-a)*W)+17+
    2*(packedKeyInputReplicaCost q W (b-a) (q-p-1)+8+100*((L+2*radius)*w+1))+
    (16*(L*(2*q+8))+19)+normalizePackedReplicaCost (8*E+8) p W L

theorem packedKeyNormalizedWorkspace_affine
    (B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N : ℕ)
    [NeZero s] :
    packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N =
      packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0+
        N*packedKeyWorkspaceReplicaCost p q W u l s t a b boundaryTarget rhsExp targetOut coreWidth k radius := by
  simp only [packedKeyNormalizedWorkspace,packedKeyComplexWorkspace]
  rw [packedKeyInputCost_affine p q W (2*N) (b-a),
    packedHaloGeometryWorkspace_affine p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*N),
    preparedNormalizePackedBatchCost_affine B p u l targetOut s t a b W N (coreLength s coreWidth k)]
  simp only [packedKeyWorkspaceReplicaCost]
  ring

/-- Native conversion is linear in the common-width halo packet. -/
theorem packedKeyInputReplicaCost_le_volume (p q W L : ℕ) (hw : 2*q+8 ≤ W) :
    packedKeyInputReplicaCost q W L (q-p-1) ≤ 56*(L*W)+9 := by
  have hd : q-p-1 ≤ W := by omega
  have hrow : 4*W+8*(2*q+8)+4*(q-p-1)+28 ≤ 44*W := by omega
  have h := Nat.mul_le_mul_left L hrow
  unfold packedKeyInputReplicaCost
  nlinarith only [h]

/-- Every replica-dependent storage charge fits the stored halo volume;
the added one covers empty cores and their constant control overhead. -/
theorem packedKeyWorkspaceReplicaCost_le_volume
    (p q W u l s t a b boundaryTarget rhsExp targetOut coreWidth k radius : ℕ) [NeZero s]
    (hhalo : coreLength s coreWidth k+2*radius ≤ b-a) (hnative : 2*q+8 ≤ W)
    (hrounded : 2*p+13 ≤ W) :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let E := inverseExecutionExponent p l targetOut B.card band
    w ≤ W → 8*E+8 ≤ W →
    packedKeyWorkspaceReplicaCost p q W u l s t a b boundaryTarget rhsExp targetOut coreWidth k radius ≤
      500*((b-a)*W+1) := by
  dsimp only
  intro hstored hnormal
  have hcore : coreLength s coreWidth k ≤ b-a := by omega
  have hpub := Nat.mul_le_mul hhalo hstored
  have hpair := Nat.mul_le_mul hcore hnative
  have hcoreWide := Nat.mul_le_mul_right W hcore
  have hinput := packedKeyInputReplicaCost_le_volume p q W (b-a) hnative
  have hnorm := normalizePackedReplicaCost_le_volume _ p W (coreLength s coreWidth k) hnormal hrounded
  unfold packedKeyWorkspaceReplicaCost
  dsimp only
  nlinarith only [hpub,hpair,hcoreWide,hinput,hnorm]

/-- The native sizing used by the executed normalized caller supplies both
format bounds, so the volume comparison needs only its common-width premise. -/
theorem packedKeyWorkspaceReplicaCost_le_volume_native
    (p q W u l s t a b targetOut coreWidth k radius : ℕ) [NeZero s]
    (hhalo : coreLength s coreWidth k+2*radius ≤ b-a) (hnative : 2*q+8 ≤ W)
    (hq : q = executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (targetOut+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) :
    packedKeyWorkspaceReplicaCost p q W u l s t a b (boundaryRecoveryTarget p (targetOut+1)) 2 targetOut coreWidth k radius ≤
      500*((b-a)*W+1) := by
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  have hqRound : q = executionPrecision p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2 B.card) 2 :=
    hq.trans (boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p (targetOut+1)) 2 B.card).1.symm
  have hround := packedRound_dimensions p u l targetOut B.card
  rw [←hqRound] at hround
  have hqE := hqRound
  rw [packedRound_precision] at hqE
  dsimp only [B,band] at hqE
  apply packedKeyWorkspaceReplicaCost_le_volume p q W u l s t a b
    (boundaryRecoveryTarget p (targetOut+1)) 2 targetOut coreWidth k radius hhalo hnative (by omega)
  · have hw : executionWidth p l (initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (targetOut+1)) 2 B.card) 2) 2 = 2*q+8 := by
      dsimp only [B,band,executionWidth]
      dsimp only [executionPrecision] at hq
      omega
    rw [hw]
    exact hnative
  · omega

/-- The entire workspace allowance is one shared numerical bank plus linear
stored data. In particular the numerical scratch never acquires a replica factor. -/
theorem packedKeyNormalizedWorkspace_le_setup_add_volume
    (B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N : ℕ)
    [NeZero s]
    (hreplica : packedKeyWorkspaceReplicaCost p q W u l s t a b boundaryTarget rhsExp targetOut coreWidth k radius ≤
      500*((b-a)*W+1)) :
    packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N ≤
      packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0+
        500*N*((b-a)*W+1) := by
  rw [packedKeyNormalizedWorkspace_affine]
  have h := Nat.mul_le_mul_left N hreplica
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
