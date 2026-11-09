module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryResourceBudgets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingNativeStock

/-! A state-independent allowance for both second interiors and their native
bank erasures. Keep this counter separate from the large execution statement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Preserve the executed second-interior witnesses through later publication.
RHS data and chosen solutions are deliberately absent from the cost contract. -/
structure CyclicSecondInteriorProfile {s : ℕ} (H K J M : ReplicaHaloProblem s)
    (p target N : ℕ) : Prop where
  leftLayout : H.SameLayout J
  rightLayout : K.SameLayout M
  leftTarget : J.target = boundaryHaloRecoveryTarget p target N
  rightTarget : M.target = boundaryHaloRecoveryTarget p target N
  leftExponent : J.rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p H.u)
  rightExponent : M.rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p H.u)

noncomputable def cyclicSecondInteriorTimeBudget {s : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (p target N : ℕ) : ℕ :=
  let rhsExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p H.u)
  (replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    H.interiorTimeBudget (boundaryHaloRecoveryTarget p target N) rhsExp)+
  (replicaCouplingNativeCleanupBound (2^15*K.p) K.precision K.wordWidth s K.t K.u K.band K.origin (K.origin+K.span)+
    K.interiorTimeBudget (boundaryHaloRecoveryTarget p target N) rhsExp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
