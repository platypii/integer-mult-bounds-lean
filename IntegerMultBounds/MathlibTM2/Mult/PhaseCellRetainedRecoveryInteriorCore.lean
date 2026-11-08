module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryInteriorCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.SchurRecoveryError
public import IntegerMultBounds.NLogN.SchurPerturbSolve
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Execute the recovery coupling and interior solve independently of the surrounding principal system. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedRecoveryInteriorCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  embProg componentReg id (recoveryInteriorCore hR hQ)

theorem retainedRecoveryInteriorCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail sourceTail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail) (embStk componentReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ xI : ZMod s → ℝ,
      v'.user = v.user ∧ n ≤ recoveryInteriorCoreCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (retainedRecoveryInteriorCore hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++S.R 110))
          132 (cstream A w (chirpLine s D)++S.R 132))}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^cExp) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) xI
        (fun i => (value q (R i)).re) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
  let E := embStk componentReg S
  obtain ⟨v₁,m,D,xI,hv₁,hm,he,hnorm,hDnorm,hxI,herror⟩ := recoveryInteriorCore_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B hB hC
    (embDn componentReg v) E tail sourceTail hready haMaster hbMaster hsource h127 h138 h143
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := componentReg) (ι := id)
    (body' := embTab componentReg (embTab groupReg body)) componentReg_injective
    (fun p => rfl) he v rfl S rfl
  refine ⟨v₂,m,D,xI,hu₂.trans hv₁,hm,he₂.cast rfl ?_,hnorm,hDnorm,hxI,herror⟩
  apply congrArg (mk v₂)
  let E₁ : Stacks 144 A := {E with R := Function.update E.R 110 (cstream A w (chirpLine s R)++S.R 110)}
  change embOvr componentReg
    ({E₁ with R := Function.update E₁.R 132 (cstream A w (chirpLine s D)++S.R 132)} : Stacks 144 A).get S = _
  rw [embOvr_updR componentReg_injective]
  dsimp only [E₁]
  rw [embOvr_updR componentReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
