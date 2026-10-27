module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRetainedSchurResidual

/-! Compute the real Schur residual in the shared-page bank with its actual numerical and readiness contracts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem sharedPageRecoveryReg_project_ports {A : ℕ} (S : Stacks 240 A)
    (input output : List (Fin (A+4))) :
    embStk sharedPageRecoveryReg {S with R := Function.update (Function.update S.R 110 input) 132 output} =
      {embStk sharedPageRecoveryReg S with R := (Function.update
        (Function.update (embStk sharedPageRecoveryReg S).R 110 input) 132 output)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110
  · subst i; rfl
  by_cases hi132 : i = 132
  · subst i; rfl
  have h110 : sharedPageRecoveryReg i ≠ 110 := sharedPageRecoveryReg_injective.ne hi110
  have h132 : sharedPageRecoveryReg i ≠ 132 := sharedPageRecoveryReg_injective.ne hi132
  simp only [embStk,Function.comp_def,Function.update_of_ne hi110,Function.update_of_ne hi132,
    Function.update_of_ne h110,Function.update_of_ne h132]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (physicalRetainedSchurResidual (P₀ := Empty) hR hQ)

theorem sharedPageSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S)))))) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D C : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,

      let input := cstream A w (chirpLine s C)++S.R 110
      let output := cstream A w (chirpLine s D)++S.R 132
      let S' : Stacks 240 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ realInteriorResidualCost p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b ∧
      Exec body (sharedPageSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S'))))) := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  let T := embStk sharedPageRecoveryReg S
  obtain ⟨v₁,n,D,R,hRsolve,hu₁,hn,he,hreal,hmag,herr,hread,hready'⟩ := physicalRetainedSchurResidual_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    B hB (embDn sharedPageRecoveryReg v) T tail h127 h138 h143 haMaster hbMaster hready
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,D,C,R,hRsolve,hu₂.trans hu₁,hn,he₂.cast rfl ?_,hreal,hmag,herr,hread,?_⟩
  · apply congrArg (mk v₂)
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 110 input}
    change embOvr sharedPageRecoveryReg ({T₀ with R := Function.update T₀.R 132 output} : Stacks 224 A).get S = _
    rw [embOvr_updR sharedPageRecoveryReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
    rfl
  · rw [sharedPageRecoveryReg_project_ports]
    exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
