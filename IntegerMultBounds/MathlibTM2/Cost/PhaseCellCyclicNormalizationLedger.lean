module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedRecoveryPiece
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedCost
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry
import Mathlib.Tactic.Linarith

/-! The actual two-piece normalizer has one setup per physical piece and linear
replica traffic. Input precision and final storage width stay distinct. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cyclicPieceNormalizationCost_affine (p q W a L replicas : ℕ) :
    PackedRecoveryNormalization.normalizationCost p q W a L replicas =
      PackedRecoveryNormalization.normalizationCost p q W a L 0+
        replicas*normalizePackedReplicaCost (2*q+8) p W L := by
  unfold PackedRecoveryNormalization.normalizationCost
  dsimp only
  rw [normalizePackedBatchCost_affine]
  ring

/-- The final storage width need only hold rounded words. The repeated bill is
linear in the sum of input and output widths, even when the former is larger. -/
theorem cyclicNormalizationCost_le_setup_add_volume (p q W s a n replicas : ℕ)
    (hW : 2*p+13 ≤ W) :
    PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) replicas+
      PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) replicas ≤
    PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) 0+
      PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) 0+
      replicas*(85*n*((2*q+8)+W)+36) := by
  have hleft := normalizePackedReplicaCost_le_volume (2*q+8) p ((2*q+8)+W)
    (min n (s-a)) (by omega) (by omega)
  have hright := normalizePackedReplicaCost_le_volume (2*q+8) p ((2*q+8)+W)
    (n-min n (s-a)) (by omega) (by omega)
  have hmono (L : ℕ) : normalizePackedReplicaCost (2*q+8) p W L ≤
      normalizePackedReplicaCost (2*q+8) p ((2*q+8)+W) L := by
    unfold normalizePackedReplicaCost
    nlinarith
  have hlen : min n (s-a)+(n-min n (s-a)) = n := by omega
  have hs : normalizePackedReplicaCost (2*q+8) p W (min n (s-a))+
      normalizePackedReplicaCost (2*q+8) p W (n-min n (s-a)) ≤
      85*n*((2*q+8)+W)+36 := by
    have hl := (hmono (min n (s-a))).trans hleft
    have hr := (hmono (n-min n (s-a))).trans hright
    have heq := congrArg (fun x => x*((2*q+8)+W)) hlen
    nlinarith only [hl,hr,heq]
  rw [cyclicPieceNormalizationCost_affine p q W a (min n (s-a)) replicas,
    cyclicPieceNormalizationCost_affine p q W 0 (n-min n (s-a)) replicas]
  nlinarith only [Nat.mul_le_mul_left replicas hs]

private theorem sum_setup_rows_le {ι : Type} (jobs : List ι) (cost setup : ι → ℕ) (B : ℕ)
    (h : ∀ k ∈ jobs, cost k ≤ setup k+B) :
    (jobs.map cost).sum ≤ (jobs.map setup).sum+jobs.length*B := by
  induction jobs with
  | nil => simp
  | cons k jobs ih =>
    have hk := h k (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hk,hs]

/-- Only the shared normalizer setup remains per call. All replica traffic
amortizes over the actual computed class, allowing per-core joint precision. -/
theorem computedFittingCyclicNormalizationSchedule_le (p W s width radius L replicas cw : ℕ)
    (hw : 0 < width) (hwidth : width ≤ s) (hradius : radius ≤ width) (hW : 2*p+13 ≤ W)
    (q : ℕ → ℕ)
    (hq : ∀ k ∈ coreGatherIndices s width radius L, 2*q k+8 ≤ cw*p) :
    let jobs := coreGatherIndices s width radius L
    let a := fun k => coreStart width k-radius
    (jobs.map (fun k => PackedRecoveryNormalization.normalizationCost p (q k) W (a k)
      (min L (s-a k)) replicas+
      PackedRecoveryNormalization.normalizationCost p (q k) W 0 (L-min L (s-a k)) replicas)).sum ≤
    (jobs.map (fun k => PackedRecoveryNormalization.normalizationCost p (q k) W (a k)
      (min L (s-a k)) 0+
      PackedRecoveryNormalization.normalizationCost p (q k) W 0 (L-min L (s-a k)) 0)).sum+
    600*replicas*s*(cw*p+W+1) := by
  dsimp only
  let jobs := coreGatherIndices s width radius L
  have hs := sum_setup_rows_le jobs
    (fun k => PackedRecoveryNormalization.normalizationCost p (q k) W (coreStart width k-radius)
      (min L (s-(coreStart width k-radius))) replicas+
      PackedRecoveryNormalization.normalizationCost p (q k) W 0 (L-min L (s-(coreStart width k-radius))) replicas)
    (fun k => PackedRecoveryNormalization.normalizationCost p (q k) W (coreStart width k-radius)
      (min L (s-(coreStart width k-radius))) 0+
      PackedRecoveryNormalization.normalizationCost p (q k) W 0 (L-min L (s-(coreStart width k-radius))) 0)
    (replicas*(85*L*(cw*p+W)+36)) (by
      intro k hk
      have h := cyclicNormalizationCost_le_setup_add_volume p (q k) W s (coreStart width k-radius) L replicas hW
      have hh := Nat.mul_le_mul_left (replicas*(85*L)) (Nat.add_le_add_right (hq k hk) W)
      nlinarith only [h,hh])
  have hv := coreGather_volume_le_six s width radius L hwidth hradius
  have hc := coreGatherIndices_length_le s width radius L hw
  have hv' := Nat.mul_le_mul_right (85*replicas*(cw*p+W)) hv
  have hc' := Nat.mul_le_mul_right (36*replicas) hc
  dsimp only [jobs] at hs
  ring_nf at hs hv' hc' ⊢
  omega

end IntegerMultBounds.MathlibTM2.Cost
