module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishComponentsSpec

/-! Finish the second recovered component and publish the complex result with restored ownership. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedRecoveryFinish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (retainedRecoveryPublishedHalo hR hQ) finishComponents

theorem retainedRecoveryFinish_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtarget : ε ≤ 1/(2 : ℝ)^recoveryTarget p (target+1))
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 148 Q A U) (S : Stacks 148 A) (residual tail sourceTail savedTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk componentReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (X : ZMod s → GaussianInt) (realTarget : ZMod s → ℝ)
    (hX : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (0 : ZMod s)
        (cstream A (executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
          (chirpLine s X)++savedTail) i) realTarget (1/(2 : ℝ)^(target+1)))
    (h145 : S.R 145 = cstream A (executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s X)++savedTail) (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let Y := fun i => realPartWord (publicationField t band a b D C i)
      let Z := cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++sourceTail
      let S' : Stacks 148 A := {S with R := Function.update (Function.update (Function.update S.R 110 tail) 145 savedTail) 132 Z}
      v'.user = v.user ∧ n ≤ recoveryToleranceCost p l s t u (target+1) rhsExp boundaryExp a b+
        finishComponentsCost q s ∧
      Exec (embTab componentReg (embTab groupReg body)) (retainedRecoveryFinish hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨realTarget i,x i⟩ : ℂ))
        (1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p)
        (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
        q l s t u band 0 0 tail (embStk componentReg S') := by
  dsimp only
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp countExp) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp countExp) rhsExp
  let band := PhaseCellBand.width p u
  let R := couplingRowField (2^15*p) q t u band a b true C B
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,herror⟩ := retainedRecoveryPublishedHalo_spec (body := body) (target := target+1)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B x ε hε hεtarget
    hB hC hxB hx v S residual tail sourceTail hresidual hready haMaster hbMaster hsource h127 h138 h143
  let Y := fun i => realPartWord (publicationField t band a b D C i)
  let input := cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)
  let output := cstream A w (chirpLine s Y)++sourceTail
  let S₁ : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
  have hproject : embStk componentReg S₁ = {(embStk componentReg S) with R :=
      (Function.update (Function.update (embStk componentReg S).R 110 input) 132 output)} := by
    have hlow : embStk componentReg {S with R := Function.update S.R 110 input} =
        {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 input} := by
      simpa [componentReg] using componentProject_updateR_inner S 110 input
    have hh : embStk componentReg S₁ =
        {(embStk componentReg {S with R := Function.update S.R 110 input}) with R :=
          (Function.update (embStk componentReg {S with R := Function.update S.R 110 input}).R 132 output)} := by
      simpa [S₁,componentReg] using
        componentProject_updateR_inner {S with R := Function.update S.R 110 input} 132 output
    rw [hlow] at hh
    exact hh
  have hready₁ : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p (target+1)) rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 input (embStk componentReg S₁) := by
    rw [hproject]
    exact (hready.update_source input).update_output output
  let E := 1/(2 : ℝ)^(target+1)
  have hX' : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s X)++savedTail) i) realTarget (1/(2 : ℝ)^(target+1)) := hX
  have hY' : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++sourceTail) i) x E := herror
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hcomplex,hready₂⟩ := finishComponents_spec (body := embTab groupReg body)
    (by omega) X Y (haloVertices s a b) (fun i => (⟨realTarget i,x i⟩ : ℂ)) E E
    (cstream A w (chirpLine s R)) (cstream A w (chirpLine s B)) tail savedTail sourceTail
    (by simp [hwq,chirpLine]) (by simp [hwq,chirpLine])
    (by simpa only [hwq] using hX') (by simpa only [hwq] using hY')
    v₁ S₁ hready₁ (by simpa [S₁,← hwq] using h145) (by simp [S₁,output,hwq])
    (by simpa [S₁] using h146) (by simpa [S₁] using h147)
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,?_,?_⟩
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h145' : k = 145 <;>
      simp [S₁,Y,w,band,← hwq,h110,h132,h145',countExp]
  · have hsum : E+E = 1/(2 : ℝ)^target := component_error_budget target
    rw [hsum] at hcomplex
    simpa [S₁,Y,w,band,← hwq,countExp,q] using hcomplex
  · convert hready₂ using 1
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h145' : k = 145 <;>
      simp [S₁,Y,w,band,← hwq,h110,h132,h145',countExp]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
