module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCyclicPassWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResumedReplicaInterior

/-! A resumed pass uses a subset of the cached first pass's storage allowance.
Reuse that comparison under the existing physical-layout equivalence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem resumedReplicaInteriorWorkspace_le_cachedPass {s : ℕ} [NeZero s]
    (H J : ReplicaHaloProblem s) (layout : H.SameLayout J)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    resumedReplicaInteriorWorkspace (A := A) (U := U) H J hR hQ ≤
      cachedReplicaPassWorkspace (A := A) (U := U) J hR hQ := by
  unfold resumedReplicaInteriorWorkspace cachedReplicaPassWorkspace
    replicaRecoveryInteriorWorkspace initializedCachedReplicaInteriorWorkspace
    cachedReplicaInteriorFinishingWorkspace
  simp only [layout.count,layout.span,layout.wordWidth]
  omega

theorem selectedResumedReplicaInteriorWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H J : ReplicaHaloProblem (Sizes.s n i), H.SameLayout J →
      J.p = Sizes.p n → J.t = Sizes.t n i →
      J.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → J.u ≤ Sizes.p n →
      J.target ≤ ct*Sizes.p n → J.rhsExp ≤ ce*Sizes.p n →
      resumedReplicaInteriorWorkspace (A := A) (U := U) H J hR hQ ≤
        4*Sizes.T n+cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce*
          J.Fs.length*J.t*J.p := by
  filter_upwards [selectedCachedReplicaPassWorkspace_le hR hQ ct ce] with n hs
  intro h i _ H J layout hp ht hl hu htarget hrhs
  exact (resumedReplicaInteriorWorkspace_le_cachedPass (A := A) (U := U) H J layout hR hQ).trans
    (hs h i J hp ht hl hu htarget hrhs)

end IntegerMultBounds.MathlibTM2.Cost
