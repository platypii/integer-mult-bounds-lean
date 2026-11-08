module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaProblemOfAxis

/-! Both cyclic pieces use the existing cached replica problem. Their ordinary
RHS, precision and stage are shared even when one piece is empty. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace RecoveryAxisBounds
variable {s t p u l : ℕ} [NeZero s] {α d : ℝ}
variable (axis : RecoveryAxisBounds s t p u l α d)
variable (target rhsExp a n : ℕ) (ha : a < s) (hn : n ≤ s)
variable (Fs : List (ZMod s → GaussianInt))
variable (hF : ∀ F ∈ Fs, ∀ k,
  ‖value (executionPrecision p l target rhsExp) (F k)‖ ≤ (2 : ℝ)^rhsExp)

noncomputable def cyclicLeftReplicaProblem : ReplicaHaloProblem s :=
  axis.replicaProblem target rhsExp a (min n (s-a))
    (calc a+min n (s-a) ≤ a+(s-a) := Nat.add_le_add_left (Nat.min_le_right n (s-a)) a
          _ = s := Nat.add_sub_of_le ha.le) Fs hF

noncomputable def cyclicRightReplicaProblem : ReplicaHaloProblem s :=
  axis.replicaProblem target rhsExp 0 (n-min n (s-a))
    (by simpa only [Nat.zero_add] using (Nat.sub_le n (min n (s-a))).trans hn) Fs hF

/-- The exact cached-driver geometry is weaker than a bound on the whole window.
Keep it separate from construction, which covers every cyclic principal window. -/
theorem cyclicReplicaProblems_cachedGeometry
    (hleft : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hright : n-min n (s-a)+PhaseCellBand.width p u ≤ s) :
    let H := axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF
    H.origin < s ∧ H.span+H.band ≤ s ∧
      K.origin < s ∧ K.span+K.band ≤ s := by
  exact ⟨ha,hleft,NeZero.pos s,hright⟩

/-- Bulk-window room suffices for both cached passes, including a seam crossing. -/
theorem cyclicReplicaProblems_cachedGeometry_of_room
    (hroom : n+PhaseCellBand.width p u ≤ s) :
    let H := axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF
    H.origin < s ∧ H.span+H.band ≤ s ∧
      K.origin < s ∧ K.span+K.band ≤ s := by
  apply axis.cyclicReplicaProblems_cachedGeometry target rhsExp a n ha hn Fs hF <;> omega

/-- The expensive setup dimensions and RHS archive agree definitionally. -/
theorem cyclicReplicaProblems_shared
    : let H := axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF
      let K := axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF
      H.Fs = K.Fs ∧ H.precision = K.precision ∧ H.wordWidth = K.wordWidth ∧
        H.stage = K.stage ∧ H.metadataWidth = K.metadataWidth := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end RecoveryAxisBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
