module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedWorkspaceSizedPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloSharedSetupBudget

/-! One explicit envelope bounds actual shared halo setup and selected-key execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

@[irreducible] def haloSharedWorkspaceEnvelope (J R K p l s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let band := PhaseCellBand.width p u
  let Z := generatedSetupScale p l target rhsExp t u band
  (288*J*(ssMulConst+1)*Z^3+100000000*(J+1)*(Z+1)^3+
    1000000*(s+t+u+band+1)*(Z+1))+
  (2*((R+1)*ringWorkspaceBudget q l w+1000*(q+l+2^l+1)*(w+1))+
    3*K*rmulCost w+180900*((2*w).size+1)*(w+1)^2+
    10000*(K+1)*(2^l+(4*p+1)+1)*(w+cExp+(8*p+1)+l+1))

theorem haloSharedSetupBudget_le_envelope (J R K p l s t u target rhsExp : ℕ) :
    haloSharedSetupBudget J R K p l s t u target rhsExp (4*p+1) ≤
      haloSharedWorkspaceEnvelope J R K p l s t u target rhsExp := by
  unfold haloSharedSetupBudget haloSharedWorkspaceEnvelope
  dsimp only
  exact Nat.add_le_add_right
    (generatedBatchSetupBudget_sized_poly J p l s t u (PhaseCellBand.width p u) target rhsExp) _

theorem generatedHaloKeysWorkspace_le_envelope
    (J R K p l s t u target rhsExp V a b : ℕ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) :
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      haloSharedWorkspaceEnvelope J R K p l s t u target rhsExp+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  apply (generatedHaloKeysWorkspace_le_budget J R K p l s t u target rhsExp V a b
    hp hs hst ha hb hθ).trans
  exact Nat.add_le_add_right (haloSharedSetupBudget_le_envelope J R K p l s t u target rhsExp) _

theorem solveHaloInteriorWorkspace_le_envelope
    (J R K p l s t u target rhsExp a b : ℕ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth P q w t u
    solveHaloInteriorWorkspace J R K p l s t u target rhsExp a b ≤
      18*initializeHaloLengthKeysCost P N q l s t u band a b+
        (haloSharedWorkspaceEnvelope J R K p l s t u target rhsExp+
          haloKeyAuxWorkspace R K p l s t u target rhsExp V) := by
  unfold solveHaloInteriorWorkspace
  dsimp only
  exact Nat.add_le_add_left (generatedHaloKeysWorkspace_le_envelope
    J R K p l s t u target rhsExp _ a b hp hs hst ha hb hθ) _

end IntegerMultBounds.MathlibTM2.Cost
