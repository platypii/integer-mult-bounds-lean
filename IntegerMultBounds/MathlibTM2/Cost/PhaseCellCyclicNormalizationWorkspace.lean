module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedRecoveryPiece

/-! The actual cyclic normalizer separates shared arithmetic scratch from linear
replica traffic. No replica-dependent arithmetic workspace is charged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The exact incremental routing/publication allowance for one replica. -/
def cyclicNormalizationReplicaWorkspace (q W L : ℕ) : ℕ :=
  16*L*(2*q+8)+18+13*(L+1)*(40*W+80)

theorem cyclicNormalizationWorkspace_eq_shared_add (p q W a L N : ℕ) :
    PackedRecoveryNormalization.normalizationWorkspace p q W a L N =
      PackedRecoveryNormalization.normalizationWorkspace p q W a L 0+
        N*cyclicNormalizationReplicaWorkspace q W L := by
  unfold PackedRecoveryNormalization.normalizationWorkspace retainedNormalizePackedRealBatchWorkspace
    normalizePackedBatchWorkspace roundPackedKeyWorkspace cyclicNormalizationReplicaWorkspace
  ring

theorem cyclicNormalizationReplicaWorkspace_le (cq p q W L : ℕ)
    (hq : q ≤ cq*p) (hp : p ≤ W) :
    cyclicNormalizationReplicaWorkspace q W L ≤ (32*cq+1800)*(L+1)*(W+1) := by
  have hqW := hq.trans (Nat.mul_le_mul_left cq hp)
  have hL := Nat.mul_le_mul_left (32*L) hqW
  unfold cyclicNormalizationReplicaWorkspace
  nlinarith only [hL,Nat.zero_le (cq*L),Nat.zero_le (cq*W),Nat.zero_le cq]

/-- Any common scale bounds the shared scalar setup and one-word scratch cubically. -/
theorem cyclicNormalizationWorkspace_zero_le {p q W a L Z : ℕ}
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hq : q ≤ Z) (hW : W ≤ Z) (ha : a ≤ Z) (hL : L ≤ Z)
    (hB : cyclicNormalizationWidth (2^15*p) q ≤ Z)
    (hsize : q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8) :
    PackedRecoveryNormalization.normalizationWorkspace p q W a L 0 ≤ 30000000*Z^3 := by
  let B := cyclicNormalizationWidth (2^15*p) q
  have htable : tblC B 0 ≤ 800*Z^2 := by
    have hs := Nat.pow_le_pow_left (show B+4 ≤ 5*Z by omega) 2
    unfold tblC
    nlinarith only [hs]
  have hbits : Nat.size (4*p) ≤ 4*Z :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.mul_le_mul_left 4 hp)
  have hproduct := Nat.mul_le_mul
    (show 2^15*p+q ≤ 32769*Z by norm_num at *; omega)
    (show 4*B+10 ≤ 14*Z by omega)
  have hscalar := Nat.mul_le_mul
    (show 18+(4*Nat.size (4*p)+31) ≤ 65*Z by omega) htable
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have hsetup : retainedRoundScalarSetupCost B p q ≤ 1000000*Z^3 := by
    unfold retainedRoundScalarSetupCost
    norm_num at hproduct ⊢
    nlinarith only [hproduct,hscalar,h₂,h₃,hB,hZ]
  have hword : topShiftWordCost (2*q+8) (q-p+inverseNormalizationShift p) (p+(p+8)+5) =
      12*(2*q+8)+22 := topShiftWordCost_eq (by omega)
  have hpub := Nat.mul_le_mul (show L+1 ≤ 2*Z by omega)
    (show 40*W+80 ≤ 120*Z by omega)
  unfold PackedRecoveryNormalization.normalizationWorkspace retainedNormalizePackedRealBatchWorkspace
    normalizePackedBatchWorkspace roundPackedKeyWorkspace generatedFinalRoundWorkspace
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
  rw [hword]
  change _ ≤ 30000000*Z^3
  change tblC B 0 ≤ _ at htable
  change retainedRoundScalarSetupCost B p q ≤ _ at hsetup
  dsimp only [B] at htable hsetup
  norm_num at htable hsetup hB ⊢
  nlinarith only [htable,hsetup,hpub,h₂,h₃,hp,hq,hW,ha,hL,hB,hZ]

end IntegerMultBounds.MathlibTM2.Cost
