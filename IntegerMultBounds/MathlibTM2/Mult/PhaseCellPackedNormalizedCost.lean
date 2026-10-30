module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyBatchCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedNormalizePackedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreRows

/-! Exact setup/replica accounting for the complete normalized local caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Rounding and common-width publication traverse only the published core. -/
def normalizePackedReplicaCost (w p W L : ℕ) : ℕ :=
  L*(26*w+16*(2*p+13)+10*W+33)+18

theorem normalizePackedBatchCost_affine (B w p W N L : ℕ) :
    normalizePackedBatchCost B w p W N L = normalizePackedBatchCost B w p W 0 L+
      N*normalizePackedReplicaCost w p W L := by
  simp only [normalizePackedBatchCost,roundPackedKeyCost,publishRoundedKeyCost,
    widenPackedKeyCost,widenPackedPrefixCost,normalizePackedReplicaCost]
  ring

/-- The common storage width pays both the native and rounded formats. -/
theorem normalizePackedReplicaCost_le_volume (w p W L : ℕ)
    (hw : w ≤ W) (hp : 2*p+13 ≤ W) :
    normalizePackedReplicaCost w p W L ≤ 85*(L*W)+18 := by
  have hsum : 26*w+16*(2*p+13)+10*W+33 ≤ 85*W := by omega
  have h := Nat.mul_le_mul_left L hsum
  unfold normalizePackedReplicaCost
  nlinarith only [h]

namespace ScalarPlacement

theorem preparedNormalizePackedBatchCost_affine (B p u l target s t a b W N L : ℕ) [NeZero s] :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u)
    preparedNormalizePackedBatchCost B p u l target s t a b W N L =
      preparedNormalizePackedBatchCost B p u l target s t a b W 0 L+
        N*normalizePackedReplicaCost (8*E+8) p W L := by
  dsimp only
  unfold preparedNormalizePackedBatchCost
  dsimp only
  rw [normalizePackedBatchCost_affine]
  ring

/-- The actual numerical, normalization and cleanup bill; scalar setup and
factor construction occur only in its zero-replica part. -/
noncomputable def packedKeyNormalizedBatchCost
    (B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N : ℕ)
    [NeZero s] : ℕ :=
  let L := coreLength s coreWidth k
  preparePackedCoreRowsCost B q L+
    (N*(26*((b-a)*W)+17)+34+
      packedKeyRealBatchCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*N))+
    (N*(16*(L*(2*q+8))+19)+22)+
    (preparedNormalizePackedBatchCost B p u l targetOut s t a b W N L+214*B+217)+
    (2*L*((2*q+8)+1)+4)

/-- One complex replica: two real RHS solves, one local split, one core pairing,
and one core normalization. All factor/geometry/scalar setup is excluded. -/
noncomputable def packedKeyNormalizedReplicaCost
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ)
    [NeZero s] : ℕ :=
  26*((b-a)*W)+17+
    2*packedKeyRealBatchReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius+
    (16*(coreLength s coreWidth k*(2*q+8))+19)+
    normalizePackedReplicaCost (2*q+8) p W (coreLength s coreWidth k)

/-- At the computed native precision, every setup is paid once per key,
including for both complex components and the final normalization pass. -/
theorem packedKeyNormalizedBatchCost_affine
    (B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N : ℕ)
    [NeZero s]
    (hq : q = 4*inverseExecutionExponent p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)) :
    packedKeyNormalizedBatchCost B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius N =
      packedKeyNormalizedBatchCost B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0+
        N*packedKeyNormalizedReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius := by
  have hw : 8*inverseExecutionExponent p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8 = 2*q+8 := by omega
  unfold packedKeyNormalizedBatchCost packedKeyNormalizedReplicaCost
  dsimp only
  rw [packedKeyRealBatchCost_two_components,preparedNormalizePackedBatchCost_affine]
  rw [hw]
  ring

/-- All format conversion and complex assembly overhead is paid by local halo
volume. No ambient length or factor construction is replicated by this bound. -/
theorem packedKeyNormalizedReplicaCost_le_local_volume
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s]
    (hcore : coreLength s coreWidth k ≤ b-a) (hhalo : 0 < b-a)
    (hnative : 2*q+8 ≤ W) (hrounded : 2*p+13 ≤ W) :
    packedKeyNormalizedReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius ≤
      2*packedKeyRealBatchReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius+
        181*((b-a)*W) := by
  have hnorm := normalizePackedReplicaCost_le_volume (2*q+8) p W (coreLength s coreWidth k) hnative hrounded
  have hcoreWidth := Nat.mul_le_mul hcore hnative
  have hcoreWide := Nat.mul_le_mul_right W hcore
  have hvolume : 1 ≤ (b-a)*W := Nat.mul_pos hhalo (by omega)
  unfold packedKeyNormalizedReplicaCost
  nlinarith only [hnorm,hcoreWidth,hcoreWide,hvolume]

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
