module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyRestoredInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRealResidualProjection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingField
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Real interior/residual output with precision-independent magnitudes and paid projection. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyRealResidualProjection : Pr P₀ 263 Q A U :=
  embProg familyCouplingSourceReg Empty.elim (realResidualProjection (P₀ := Empty))

theorem familyRealResidualProjection_exec (hA : 4 ≤ A) (q s : ℕ)
    (D R : List GaussianInt) (interiorTail rhsTail : List (Fin (A+4)))
    (hDlen : D.length = s) (hRlen : R.length = s)
    (v : HS 263 Q A U) (S : Stacks 263 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hD : S.R 132 = cstream A (2*q+8) D++interiorTail)
    (hR : S.R 110 = cstream A (2*q+8) R++rhsTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ realResidualProjectionCost q s ∧
      Exec body familyRealResidualProjection (mk v S) m
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A (2*q+8) (D.map realPartWord)++interiorTail))
          110 (cstream A (2*q+8) (R.map realPartWord)++rhsTail))}) := by
  let e := familyCouplingSourceReg
  let T := embStk e S
  obtain ⟨vi,m,hu,hm,he⟩ := realResidualProjection_exec (body := fun p : Empty => nomatch p)
    hA q s D R interiorTail rhsTail hDlen hRlen (embDn e v) T hq hs hD hR h94 h131 h134 h135
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyCouplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T₁ : Stacks 144 A := {T with R := (Function.update T.R 132
    (cstream A (2*q+8) (D.map realPartWord)++interiorTail))}
  change embOvr e ({T₁ with R := (Function.update T₁.R 110
    (cstream A (2*q+8) (R.map realPartWord)++rhsTail))} : Stacks 144 A).get S = _
  rw [embOvr_updR familyCouplingSourceReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR familyCouplingSourceReg_injective,embOvr_stk]
  rfl


noncomputable def familyRealInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  .seq (familyRestoredInteriorResidual recovery hR hQ) familyRealResidualProjection

def familyRealInteriorResidualCost (A p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  familyRestoredInteriorResidualCost A p l s t u target rhsExp a b+
    realResidualProjectionCost (executionPrecision p l target rhsExp) s

theorem familyRealInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 263 Q A U) (S : Stacks 263 A) (borrowed pageTail familyTail : List (Fin (A+4)))
    (h127 : (embStk familyCouplingSourceReg S).R 127 = []) (h138 : (embStk familyCouplingSourceReg S).R 138 = [])
    (haMaster : ((embStk familyCouplingSourceReg S).R 141).length = a) (hbMaster : ((embStk familyCouplingSourceReg S).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk familyCouplingSourceReg S))
    (h143 : (embStk familyCouplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S))
    (hfamily : S.R 260 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b))++familyTail)
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let e := stableInteriorExponent p rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let R := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (C i))
      v'.user = v.user ∧ n ≤ familyRealInteriorResidualCost A p l s t u target rhsExp a b ∧
      Exec body (familyRealInteriorResidual recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
          110 (cstream A w (chirpLine s R)++S.R 110))}) ∧
      (∀ i, (D i).im = 0) ∧
      (∀ i ∈ haloInterior s t band a b, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target) ∧
      (∀ i, (R i).im = 0) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp e (8*p+1) (couplingCountExponent p u)) ∧
      ∀ i ∈ haloBoundary s t band a b, |(value q (R i)).re-((value q (C i)).re-
        SchurDominance.couple (realMatrix s t p u) (haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^e*(1/(2 : ℝ)^q))+2*(1/(2 : ℝ)^target) := by
  dsimp only
  let countExp := couplingCountExponent p u
  have hcount := couplingCountExponent_spec p u
  have hcountBudget := couplingCountExponent_le_execution p u l target rhsExp
  have hmass := couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  let : NeZero t := ⟨by omega⟩
  have hrowWidth := interiorResidual_width hcountBudget
  have hdom := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,hDnorm,hDerror,hRnorm,hRerror⟩ := familyRestoredInteriorResidual_spec
    (body := body) recovery hR hQ hA hp0 hst hu hαu hθ0 hgap hbudget hband has hbs hpad C hC x hx
    v S borrowed pageTail familyTail h127 h138 haMaster hbMaster hready h143 hcache hfamily hfamilyFresh hcount hrowWidth 2 hmass
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  let S₁ : Stacks 263 A := {S with R := (Function.update
    (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
    110 (cstream A w (chirpLine s R)++S.R 110))}
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hproj : embStk familyCouplingSourceReg S₁ =
      {embStk familyCouplingSourceReg S with R := (Function.update
        (Function.update (embStk familyCouplingSourceReg S).R 132 (cstream A w (chirpLine s D)++S.R 132))
        110 (cstream A w (chirpLine s R)++S.R 110))} := by
    let V : Stacks 263 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)}
    change embStk familyCouplingSourceReg {V with R := Function.update V.R (familyCouplingSourceReg 110) _} = _
    rw [embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective]
    dsimp only [V]
    have h132 := embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective S 132
      (cstream A w (chirpLine s D)++S.R 132)
    change embStk familyCouplingSourceReg {S with R := Function.update S.R 132 _} = _ at h132
    rw [h132]
  have hqS : (S₁.R 119).length = q := by
    change ((embStk familyCouplingSourceReg S₁).R 119).length = q
    rw [hproj]
    simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hsS : (S₁.R 121).length = s := by
    change ((embStk familyCouplingSourceReg S₁).R 121).length = s
    rw [hproj]
    simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := familyRealResidualProjection_exec (body := body)
    (by omega) q s (chirpLine s D) (chirpLine s R) (S.R 132) (S.R 110) (by simp) (by simp) v₁ S₁
    hqS hsS
    (by simp [S₁,hw]) (by simp [S₁,hw])
    (by change (embStk familyCouplingSourceReg S₁).R 94 = []; rw [hproj]; simpa using hready.blank 94 (by decide) (by decide) (by decide))
    (by change (embStk familyCouplingSourceReg S₁).R 131 = []; rw [hproj]; simpa using hready.fresh 131 (by simp))
    (by change (embStk familyCouplingSourceReg S₁).R 134 = []; rw [hproj]; simpa using hready.fresh 134 (by simp))
    (by change (embStk familyCouplingSourceReg S₁).R 135 = []; rw [hproj]; simpa using hready.fresh 135 (by simp))
  let D' := fun i => realPartWord (D i)
  let C' := fun i => realPartWord (C i)
  have hD' : ∀ i ∈ haloInterior s t band a b,
      ‖value q (D' i)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp :=
    stableInterior_norm hp0 _ hdom C D hC x hx hDerror
  have hR' : ∀ i, ‖value q (guardedCouplingRowField (2^15*p) q t u band a b false D' C' i)‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) countExp :=
    guardedCouplingRowField_norm false hp0 hst hαu hθ0 hgap hbudget D' C' hcount
      (fun i => by
        rw [value_realPartWord_norm]
        exact (Complex.abs_re_le_norm _).trans (hC i)) hD'
  refine ⟨v₂,n₁+n₂,D',hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,fun i => rfl,hD',?_,?_,hR',?_⟩
  · apply congrArg (mk v₂)
    simp only [hw]
    have hDline : (chirpLine s D).map realPartWord = chirpLine s D' := by
      simp [chirpLine,D',List.map_map,Function.comp_def]
    have hRline : (chirpLine s R).map realPartWord =
        chirpLine s (guardedCouplingRowField (2^15*p) q t u band a b false D' C') := by
      simp [chirpLine,R,D',C',List.map_map,Function.comp_def,guardedCouplingRowField_realPart]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [S₁,hDline,hRline,hk110,hk132,q,w,band,C']
  · simpa only [D',value_realPartWord_re] using hDerror
  · intro i
    rw [← guardedCouplingRowField_realPart]
    rfl
  · intro i hi
    have hsharpWidth : q+couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) countExp+2 ≤ w := stableInteriorResidual_width p u l target rhsExp
    have hC' (i) : ‖value q (C' i)‖ ≤ (2 : ℝ)^rhsExp := by
      rw [value_realPartWord_norm]
      exact (Complex.abs_re_le_norm _).trans (hC i)
    have hpoint := guardedCouplingRowField_error (A := A) (w := w) (rhsExp := rhsExp)
      (inputExp := stableInteriorExponent p rhsExp) (countExp := countExp) false hA
      hp0 hst hαu hθ0 hgap hbudget hsharpWidth D' C' x (fun i => (value q (C i)).re)
      2 (1/(2 : ℝ)^target) 0 (by positivity) hcount hC' hD'
      (by intro j hj; simpa only [D',value_realPartWord_re,Real.norm_eq_abs] using hDerror j hj)
      hmass (by intro j; simp [C']) hbs i (Or.inr hi)
    simpa only [Bool.false_eq_true,ite_false,add_zero] using hpoint

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
