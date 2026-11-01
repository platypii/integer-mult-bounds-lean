module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedCachedReplicaCouplingStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCouplingSetup

/-! The actual shared workspace reuses the existing shared-setup time envelope.
Only the linear clock and one numerical transition reserve remain outside it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem releasedCachedReplicaCouplingWorkspace_shared_le {s : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (K : ℕ) :
    releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K ≤
      (26+mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U)))*
        cachedReplicaCouplingSharedTime H+(8*H.Fs.length+8)+
          cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K H.metadataWidth := by
  have hpoly (h g p m c r retire clock worker : ℕ) :
      2*h+(24*(g+p+c)+r*m+(clock+worker)) ≤
        (26+r)*(h+(g+p+m+c)+retire)+clock+worker := by
    nlinarith only [Nat.zero_le (r*h),Nat.zero_le (r*g),Nat.zero_le (r*p),Nat.zero_le (r*c),
      Nat.zero_le ((26+r)*retire)]
  simpa only [releasedCachedReplicaCouplingWorkspace,preparedCachedReplicaCouplingWorkspace,
    initializeCachedReplicaCouplingRuntimeWorkspace,cachedReplicaCouplingSharedTime,
    initializeCachedReplicaCouplingRuntimeCost,Nat.add_sub_cancel_left] using
    hpoly (replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span))
      (prepareReplicaCouplingGeometryCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span))
      (sharedCouplingCoefficientIntervalCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) H.metadataWidth)
      (initializeRecoveryMasksCost H.metadataWidth H.span H.band)
      (replicaCouplingCountersCost H.precision H.wordWidth H.band)
      (mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U)))
      (4*(H.span+H.band)+4) (8*H.Fs.length+8)
      (cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K H.metadataWidth)

theorem selectedReleasedCachedCouplingWorkspace_shared_le (cw cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ (H : ReplicaHaloProblem (Sizes.s n i)) (K : ℕ), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.u ≤ H.p → H.metadataWidth ≤ cV*H.p →
      releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K ≤
        Sizes.T n+(8*H.Fs.length+8)+
          cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K H.metadataWidth := by
  let scale := 26+mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U))
  filter_upwards [selectedCachedReplicaCouplingSharedTime_volume_le cw cV scale] with n hs
  intro h i _ H K hp ht hw hu hV
  have hc := hs h i H hp ht hw hu hV
  exact (releasedCachedReplicaCouplingWorkspace_shared_le H K).trans
    (Nat.add_le_add_right (Nat.add_le_add_right hc _) _)

end IntegerMultBounds.MathlibTM2.Cost
