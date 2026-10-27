module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift

/-! Retained residual execution and readiness in the full physical boundary bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def physicalRetainedSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  embProg boundaryFactorLegacyReg id (embProg tableReg id
    (embProg boundaryArithmeticReg id (retainedSchurResidual hR hQ)))

theorem physicalRetainedSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))))) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++S.R 110
      let output := cstream A w (chirpLine s D)++S.R 132
      let S' : Stacks 224 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ realInteriorResidualCost p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (physicalRetainedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) := by
  dsimp only
  let S₀ := embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S))
  let v₀ := embDn boundaryArithmeticReg (embDn tableReg (embDn boundaryFactorLegacyReg v))
  have h127₀ : S₀.R 127 = [] := by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h127
  have h138₀ : S₀.R 138 = [] := by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h138
  have h143₀ : S₀.R 143 = [] := by simpa [S₀,embStk,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using h143
  have ha₀ : (S₀.R 141).length = a := haMaster
  have hb₀ : (S₀.R 142).length = b := hbMaster
  obtain ⟨v₁,n,D,R,hRsolve,hu₁,hn,he,hreal,hmag,herr,hread,hready'⟩ :=
    retainedSchurResidual_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad B hB v₀ S₀ tail h127₀ h138₀ h143₀ ha₀ hb₀ hready
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  have he' : Exec (embTab componentReg (embTab groupReg body)) (retainedSchurResidual hR hQ)
      (mk v₀ S₀) n (mk v₁ {S₀ with R := Function.update (Function.update S₀.R 110 input) 132 output}) := he
  obtain ⟨v₂,hu₂,he₂⟩ := boundary_retained_residual_lift
    (embTab componentReg (embTab groupReg body)) (retainedSchurResidual hR hQ)
    v S v₁ n input output hu₁ he'
  refine ⟨v₂,n,D,R,hRsolve,hu₂,hn,he₂,hreal,hmag,herr,hread,?_⟩
  rw [boundary_retained_project_outputs]
  exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
