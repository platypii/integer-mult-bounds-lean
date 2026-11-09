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

/-- Physical format reuse bounds both numerical parameters, even though the
second pass changes its target, source data and reference solution. -/
theorem CyclicSecondInteriorProfile.numerical_bounds {s : ℕ}
    {H K J L : ReplicaHaloProblem s} {p target N t l c : ℕ}
    (profile : CyclicSecondInteriorProfile H K J L p target N)
    (hbase : ∀ D ∈ [H,K], D.p = p ∧ D.t = t ∧ D.l = l ∧
      D.u ≤ p ∧ D.wordWidth ≤ c*p) :
    ∀ D ∈ [H,K,J,L], D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧
      D.target ≤ c*p ∧ D.rhsExp ≤ c*p := by
  have transfer (D E : ReplicaHaloProblem s) (layout : D.SameLayout E)
      (hD : D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧ D.wordWidth ≤ c*p) :
      E.p = p ∧ E.t = t ∧ E.l = l ∧ E.u ≤ p ∧ E.wordWidth ≤ c*p := by
    simpa only [layout.p,layout.t,layout.l,layout.u,layout.wordWidth] using hD
  have hH := hbase H (by simp)
  have hK := hbase K (by simp)
  have hJ := transfer H J profile.leftLayout hH
  have hL := transfer K L profile.rightLayout hK
  intro D hD
  have hb : D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧ D.wordWidth ≤ c*p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · exact hH
    · exact hK
    · exact hJ
    · exact hL
  have hparameters : D.target ≤ D.wordWidth ∧ D.rhsExp ≤ D.wordWidth := by
    unfold ReplicaHaloProblem.wordWidth executionWidth executionExponent inputExponent sourceExponent
    omega
  exact ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,
    hparameters.1.trans hb.2.2.2.2,hparameters.2.trans hb.2.2.2.2⟩

noncomputable def cyclicSecondInteriorTimeBudget {s : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (p target N : ℕ) : ℕ :=
  let rhsExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p H.u)
  (replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    H.interiorTimeBudget (boundaryHaloRecoveryTarget p target N) rhsExp)+
  (replicaCouplingNativeCleanupBound (2^15*K.p) K.precision K.wordWidth s K.t K.u K.band K.origin (K.origin+K.span)+
    K.interiorTimeBudget (boundaryHaloRecoveryTarget p target N) rhsExp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
