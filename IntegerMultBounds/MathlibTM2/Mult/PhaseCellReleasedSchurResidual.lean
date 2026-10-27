module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireInitialInteriorReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitialErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! Execute the initial Schur pass and release its temporary interior stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def releasedSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (retainedSchurResidual hR hQ) retireInitialInterior

def releasedSchurResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  realInteriorResidualCost p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b+
    retireInitialInteriorCost (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) s

theorem releasedSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S)) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let input := cstream A w (chirpLine s C)++S.R 110
      let S' : Stacks 148 A := {S with R := Function.update S.R 110 input}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ releasedSchurResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab componentReg (embTab groupReg body)) (releasedSchurResidual hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk componentReg S') := by
  dsimp only
  let firstTarget := initialSchurTarget p u target rhsExp
  let q := executionPrecision p l firstTarget rhsExp
  let w := executionWidth p l firstTarget rhsExp
  let band := PhaseCellBand.width p u
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,n₁,D,R,hRsolve,hu₁,hn₁,he₁,hCreal,hCnorm,hCerror,hread,hready₁⟩ := retainedSchurResidual_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B hB v S tail
    h127 h138 h143 haMaster hbMaster hready
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  let S₁ : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₁) := hready₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hready₂⟩ := retireInitialInterior_ready (body := embTab groupReg body)
    (cstream A w (chirpLine s D)) (S.R 132) input (by simp [chirpLine,hwq]) v₁ S₁ hready₁'
    (by simp [S₁,output]) (by simpa [S₁] using h147)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 132 (S.R 132)}
  let Sfinal : Stacks 148 A := {S with R := Function.update S.R 110 input}
  have hframe : S₂ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
      simp [S₂,S₁,Sfinal,h110,h132]
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) retireInitialInterior
      (mk v₁ S₁) n₂ (mk v₂ S₂) := he₂
  rw [hframe] at he₂'
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₂) := hready₂
  rw [hframe] at hready₂'
  refine ⟨v₂,n₁+n₂,D,R,hRsolve,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂',hCreal,hCnorm,hCerror,?_,hready₂'⟩
  simpa [Sfinal,S₁,input,C,q,w,band,firstTarget] using hread

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
