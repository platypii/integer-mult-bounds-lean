module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWorkspaceCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Selected bounds for the packed caller's linear storage allowance. Shared
factor construction and numerical scratch remain in its separate zero-replica bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The packed caller's own storage bill is polynomial in a selected axis.
This uses its native precision, rather than a bill for the older family solver. -/
theorem selectedPackedWorkspaceReplica_poly_le (cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (q W u a b target coreWidth k radius : ℕ)
    (hb : b ≤ Sizes.s n i)
    (hhalo : coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a)
    (hnative : 2*q+8 ≤ W) (hwide : W ≤ cw*Sizes.p n)
    (hq : q = executionPrecision (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (initialSchurTarget (Sizes.p n) u
        (boundaryTableBits (Sizes.p n) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
          (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card) 2) 2) :
    packedKeyWorkspaceReplicaCost (Sizes.p n) q W u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b
      (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 target coreWidth k radius ≤
        (500*(cw+1))*Sizes.t n i*Sizes.p n := by
  have hr := packedKeyWorkspaceReplicaCost_le_volume_native (Sizes.p n) q W u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
    a b target coreWidth k radius hhalo hnative hq
  have hlength : b-a ≤ Sizes.t n i := (Nat.sub_le b a).trans (hb.trans (h.good.lt i).le)
  have hv := Nat.mul_le_mul hlength hwide
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hunit : 1 ≤ Sizes.t n i*Sizes.p n := Nat.mul_pos ht hp
  nlinarith only [hr,hv,hunit]

/-- Reprice the actual normalized caller's workspace. The zero-replica bill
is retained once, while only stored data is multiplied by the replica count. -/
theorem selectedPackedNormalizedWorkspace_le_shared_add_linear (cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (q W u a b target coreWidth k radius Bcore V N : ℕ)
    (hb : b ≤ Sizes.s n i)
    (hhalo : coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a)
    (hnative : 2*q+8 ≤ W) (hwide : W ≤ cw*Sizes.p n)
    (hq : q = executionPrecision (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (initialSchurTarget (Sizes.p n) u
        (boundaryTableBits (Sizes.p n) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
          (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card) 2) 2) :
    packedKeyNormalizedWorkspace Bcore (Sizes.p n) q W u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b V (boundaryRecoveryTarget (Sizes.p n) (target+1)) (target+1) 2 target coreWidth k radius N ≤
      packedKeyNormalizedWorkspace Bcore (Sizes.p n) q W u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b V (boundaryRecoveryTarget (Sizes.p n) (target+1)) (target+1) 2 target coreWidth k radius 0+
        (500*(cw+1))*N*Sizes.t n i*Sizes.p n := by
  rw [packedKeyNormalizedWorkspace_affine]
  have hr := Nat.mul_le_mul_left N
    (selectedPackedWorkspaceReplica_poly_le cw h i q W u a b target coreWidth k radius hb hhalo hnative hwide hq)
  apply Nat.add_le_add_left
  convert hr using 1 <;> ring

/-- Any fixed multiple of one replica's local storage is negligible relative
to the selected global volume. Batch storage is still charged per replica. -/
theorem selectedPackedWorkspaceReplica_scaled_volume_le (cw scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ q W u a b target coreWidth k radius : ℕ,
      b ≤ Sizes.s n i → coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      2*q+8 ≤ W → W ≤ cw*Sizes.p n →
      q = executionPrecision (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (initialSchurTarget (Sizes.p n) u
          (boundaryTableBits (Sizes.p n) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
            (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card) 2) 2 →
      scale*packedKeyWorkspaceReplicaCost (Sizes.p n) q W u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b
        (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 target coreWidth k radius ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (scale*(500*(cw+1))) 1 1] with n hv
  intro h i _ q W u a b target coreWidth k radius hb hhalo hn hw hq
  have hr := Nat.mul_le_mul_left scale
    (selectedPackedWorkspaceReplica_poly_le cw h i q W u a b target coreWidth k radius hb hhalo hn hw hq)
  exact hr.trans (by convert hv i using 1 <;> ring)

end IntegerMultBounds.MathlibTM2.Cost
