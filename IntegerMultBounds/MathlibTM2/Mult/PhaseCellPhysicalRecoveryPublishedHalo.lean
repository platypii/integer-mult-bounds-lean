module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift

/-! Execute recovery in the physical boundary bank while retaining its owned pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def physicalRecoveryPublishedHalo (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  embProg boundaryFactorLegacyReg id (embProg tableReg id
    (embProg boundaryArithmeticReg id (retainedRecoveryPublishedHalo hR hQ)))

theorem physicalRecoveryPublishedHalo_at_precision (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target workingTarget rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (htarget : target ≤ workingTarget)
    (hεtarget : ε ≤ 1/(2 : ℝ)^recoveryTarget p target)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hCreal : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, (C i).im = 0)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 224 Q A U) (S : Stacks 224 A) (residual tail sourceTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ recoveryToleranceCost p l s t u workingTarget rhsExp a b ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (physicalRecoveryPublishedHalo hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s)
          (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail) i) x
        (1/(2 : ℝ)^target) := by
  dsimp only
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp boundaryExp countExp) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp boundaryExp countExp) rhsExp
  let band := PhaseCellBand.width p u
  let R := couplingRowField (2^15*p) q t u band a b true C B
  let S₀ := embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))
  let v₀ := embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))
  obtain ⟨v₁,n,D,hu₁,hn,he,herror⟩ := retainedRecoveryPublishedHalo_at_precision (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B x ε hε htarget hεtarget
    hB hCreal hxB hx v₀ S₀ residual tail sourceTail hresidual hready
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using haMaster)
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hbMaster)
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hsource)
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h127)
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h138)
    (by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h143)
  let input := cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)
  let output := cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail
  obtain ⟨v₂,hu₂,he₂⟩ := boundary_retained_residual_lift
    (embTab componentReg (embTab groupReg body)) (retainedRecoveryPublishedHalo hR hQ)
    v S v₁ n input output hu₁ he
  exact ⟨v₂,n,D,hu₂,hn,he₂,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
