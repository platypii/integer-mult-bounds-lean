module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyRetainedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryRhs

/-! Compute an interior Schur residual and gather its actual boundary RHS on the retained factor page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyComputedBoundaryRhs (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyRetainedSchurResidual recovery hR hQ) familyBoundaryRhs

theorem familyComputedBoundaryRhs_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 263 Q A U) (S : Stacks 263 A) (tail pageTail familyTail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk familyCouplingSourceReg S))
    (hcache : CouplingPageCacheReady recovery (2^15*p)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp)
      (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp)
      s t u (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A
      (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp)
      (2^15*p) s t u (PhaseCellBand.width p u) a b (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = [])
    (V : ℕ) (hsV : s ≤ 2^V) (coordinateTail : List (Fin (A+4)))
    (hN : (S.R 116).length = (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hV : (S.R 115).length = V)
    (hw : (S.R 160).length = executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s (haloBoundary s t (PhaseCellBand.width p u) a b)).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 263, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let boundary := haloBoundary s t band a b
    ∃ v' n, ∃ D C : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,

      let input := cstream A w (chirpLine s C)++S.R 110
      let output := cstream A w (chirpLine s D)++S.R 132
      let S' : Stacks 263 A := {S with R := (Function.update
        (Function.update (Function.update S.R 110 input) 132 output) 206
        (cstream A w ((List.range boundary.card).map (fun j => C (bFoldAt s boundary j)))++S.R 206))}
      (∀ c, SchurDominance.Solves (realMatrix s t p u) I (R c) c) ∧
      v'.user = v.user ∧ n ≤ familyRealInteriorResidualCost A p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b+
        boundaryRhsPrepareCost V w boundary.card s ∧
      Exec body (familyComputedBoundaryRhs recovery hR hQ) (mk v S) n (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ boundary, 8*p*|(value q (C i)).re-SchurDominance.residual (realMatrix s t p u) I R
          (fun i => (value q (B i)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      (∀ i, publishedCellRead q w (0 : ZMod s) (S'.R 110) i = (value q (C i)).re) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) q l s t u band 0 0 input
        (embStk familyCouplingSourceReg S') := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  let boundary := haloBoundary s t band a b
  obtain ⟨v₁,n₁,D,R,hRsolve,hu₁,hn₁,he₁,hreal,hmag,herr,hread,hready'⟩ := familyRetainedSchurResidual_spec
    (body := body) recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    B hB v S tail pageTail familyTail h127 h138 h143 haMaster hbMaster hready hcache hfamily hfamilyFresh
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let input := cstream A w (chirpLine s C)++S.R 110
  let output := cstream A w (chirpLine s D)++S.R 132
  let S₁ : Stacks 263 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
  have hz : ∀ r : Fin 263, 1 ≤ r.val → r.val < 7 → S₁.R r = [] := by
    intro r hr1 hr7
    have h110 : r ≠ 110 := by intro he; subst r; simp at hr7
    have h132 : r ≠ 132 := by intro he; subst r; simp at hr7
    simpa [S₁,h110,h132] using hblank r hr1 hr7
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := familyBoundaryRhs_exec (body := body) boundary V w
    (Nat.le_trans (by decide : 4 ≤ 96) hA) hsV C C (by intro i hi; rfl) coordinateTail (S.R 110) v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hV) (by simpa [S₁] using hw)
    (by simpa [S₁] using hcoordinates) (by rfl)
    (by simpa [S₁] using h0) (by simpa [S₁] using h106) (by simpa [S₁] using h139) hz
  refine ⟨v₂,n₁+n₂,D,C,R,hRsolve,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,hreal,hmag,herr,?_,?_⟩
  · apply congrArg (mk v₂)
    rfl
  · exact hread
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk familyCouplingSourceReg {S₁ with R := Function.update S₁.R 206 _})
    rw [familyCouplingSource_high_update S₁ 206 (by decide)]
    exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
