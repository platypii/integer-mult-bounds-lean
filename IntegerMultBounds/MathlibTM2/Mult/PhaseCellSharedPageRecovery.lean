module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo

/-! Execute recovery in the shared-page bank, preserving all factor and publication setup tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def sharedPageRecoveryReg (i : Fin 224) : Fin 240 := ⟨i.val,by omega⟩

theorem sharedPageRecoveryReg_injective : Function.Injective sharedPageRecoveryReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 240 => k.val) h)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

noncomputable def sharedPageRecoveryPublishedHalo (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (physicalRecoveryPublishedHalo (P₀ := Empty) hR hQ)

theorem sharedPageRecoveryPublishedHalo_at_precision (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 240 Q A U) (S : Stacks 240 A) (residual tail sourceTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg S))))))
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
      Exec body (sharedPageRecoveryPublishedHalo hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s)
          (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail) i) x
        (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget)
    rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget)
    rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
  let band := PhaseCellBand.width p u
  let R := couplingRowField (2^15*p) q t u band a b true C B
  let T := embStk sharedPageRecoveryReg S
  obtain ⟨v₁,n,D,hu₁,hn,he,herror⟩ := physicalRecoveryPublishedHalo_at_precision
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    C B x ε hε htarget hεtarget hB hCreal hxB hx
    (embDn sharedPageRecoveryReg v) T residual tail sourceTail hresidual hready
    haMaster hbMaster hsource h127 h138 h143
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,D,hu₂.trans hu₁,hn,he₂.cast rfl ?_,herror⟩
  apply congrArg (mk v₂)
  let input := cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)
  let output := cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 110 input}
  change embOvr sharedPageRecoveryReg ({T₀ with R := Function.update T₀.R 132 output} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
