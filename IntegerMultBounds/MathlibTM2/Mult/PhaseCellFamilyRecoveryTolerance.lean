module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryMagnitude

/-! Execute recovery/publication with an allocated uniform dyadic error target. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyRecoveryToleranceCost (A p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  familyRecoveryPublishedHaloCost A p l s t u (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u) a b

theorem familyRecoveryPublishedHalo_tolerance_at_precision (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 263 Q A U) (S : Stacks 263 A) (residual tail sourceTail pageTail familyTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk familyCouplingSourceReg S))
    (haMaster : ((embStk familyCouplingSourceReg S).R 141).length = a) (hbMaster : ((embStk familyCouplingSourceReg S).R 142).length = b)
    (hsource : (embStk familyCouplingSourceReg S).R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : (embStk familyCouplingSourceReg S).R 127 = []) (h138 : (embStk familyCouplingSourceReg S).R 138 = []) (h143 : (embStk familyCouplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) s t u (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (2^15*p) s t u (PhaseCellBand.width p u) a b (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ familyRecoveryToleranceCost A p l s t u workingTarget rhsExp a b ∧
      Exec body (familyRecoveryPublishedHalo recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s)
          (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail) i) x
        (1/(2 : ℝ)^target) := by
  dsimp only
  let boundaryExp := stableInteriorExponent p rhsExp
  have hεone : ε ≤ 1 := hεtarget.trans
    ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  have hC := haloBoundary_norm hp hwidth hα hst hαu hθ hgap hbudget B C hB hCreal x hx hεone
    (by intro i hi; simpa only [Real.norm_eq_abs] using hxB i hi)
  obtain ⟨v',n,D,hu,hn,he,herror⟩ := familyRecoveryPublishedHalo_spec (body := body) (target := recoveryTarget p workingTarget)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B x ε hε
    hB hC hxB hx v S residual tail sourceTail pageTail familyTail hresidual hready haMaster hbMaster hsource h127 h138 h143 hcache hfamily hfamilyFresh
  refine ⟨v',n,D,hu,hn,he,?_⟩
  intro i hi
  exact (herror i hi).trans (selected_recovery_error_budget_of_le p u l target workingTarget rhsExp boundaryExp htarget hεtarget)

theorem familyRecoveryPublishedHalo_tolerance (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtarget : ε ≤ 1/(2 : ℝ)^recoveryTarget p target)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hCreal : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, (C i).im = 0)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 263 Q A U) (S : Stacks 263 A) (residual tail sourceTail pageTail familyTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk familyCouplingSourceReg S))
    (haMaster : ((embStk familyCouplingSourceReg S).R 141).length = a) (hbMaster : ((embStk familyCouplingSourceReg S).R 142).length = b)
    (hsource : (embStk familyCouplingSourceReg S).R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : (embStk familyCouplingSourceReg S).R 127 = []) (h138 : (embStk familyCouplingSourceReg S).R 138 = []) (h143 : (embStk familyCouplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp) s t u (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A
      (executionWidth p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
      (2^15*p) s t u (PhaseCellBand.width p u) a b (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ familyRecoveryToleranceCost A p l s t u target rhsExp a b ∧
      Exec body (familyRecoveryPublishedHalo recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail))}) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s)
          (cstream A w (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++sourceTail) i) x
        (1/(2 : ℝ)^target) := by
  exact familyRecoveryPublishedHalo_tolerance_at_precision (body := body) recovery hR hQ hA hp hwidth hα hst hu hαu
    hθ hgap hbudget hband has hbs hpad C B x ε hε (le_refl target) hεtarget hB hCreal hxB hx
    v S residual tail sourceTail pageTail familyTail hresidual hready haMaster hbMaster hsource h127 h138 h143 hcache hfamily hfamilyFresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
