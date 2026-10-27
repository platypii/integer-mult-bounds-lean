module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilyInteriorForCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedFeedCouplingPass

/-! Execute the retained-family interior pass and the cached boundary residual
pass in the enlarged inverse workspace. Both numerical cache kinds survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

noncomputable def familyInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  .seq (placedFamilyInteriorForCoupling hR hQ)
    (embProg familyInverseLegacyReg Empty.elim (placedCachedFeedCouplingPass (P₀ := Empty) recovery hQ false))

def familyInteriorResidualCost (A p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  familyInitializedInteriorCost A p l s t u target rhsExp a b+
    installCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) a b+
    placedCachedFeedCouplingPassCost false (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t (PhaseCellBand.width p u) a b
      (couplingCoefficientPage (2^15*p) (executionPrecision p l target rhsExp)
        s t u (PhaseCellBand.width p u) a b s).length

theorem familyInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b countExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
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
    (hfamilyFresh : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = [])
    (hcount : 2*PhaseCellBand.width p u+1 ≤ 2^countExp)
    (hrowWidth : executionPrecision p l target rhsExp+
      couplingRowExponent rhsExp (interiorOutputExponent p l target rhsExp) (8*p+1) countExp+2 ≤
        executionWidth p l target rhsExp)
    (K : ℝ) (hmass : ∀ i < s, (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i (i+δ) : ℝ)|)).sum ≤ K) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let e := interiorOutputExponent p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
      let T : Stacks 263 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)}
      let H : Stacks 144 A := {embStk familyCouplingSourceReg T with R :=
        (couplingHeadersR (2^15*p) q s t u band a b (embStk familyCouplingSourceReg T).R)}
      let G := embOvr familyCouplingSourceReg H.get T
      v'.user = v.user ∧ n ≤ familyInteriorResidualCost A p l s t u target rhsExp a b ∧
      Exec body (familyInteriorResidual recovery hR hQ) (mk v S) n
        (mk v' {G with R := Function.update G.R 110 (cstream A w (chirpLine s R)++G.R 110)}) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp e (8*p+1) countExp) ∧
      ∀ i ∈ haloBoundary s t band a b, |(value q (R i)).re-((value q (C i)).re-
        SchurDominance.couple (realMatrix s t p u) (haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^e*(1/(2 : ℝ)^q))+K*(1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let e := interiorOutputExponent p l target rhsExp
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,hcoupling,hfamilyG,hDnorm,hDerror⟩ := placedFamilyInteriorForCoupling_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S borrowed familyTail
    h127 h138 haMaster hbMaster hready hfamily hfamilyFresh
  let output := cstream A w (chirpLine s D)++S.R 132
  let T : Stacks 263 A := {S with R := Function.update S.R 132 output}
  let H : Stacks 144 A := {embStk familyCouplingSourceReg T with R := couplingHeadersR (2^15*p) q s t u band a b (embStk familyCouplingSourceReg T).R}
  let G := embOvr familyCouplingSourceReg H.get T
  have hT : embStk familyCouplingSourceReg T =
      {embStk familyCouplingSourceReg S with R := Function.update (embStk familyCouplingSourceReg S).R 132 output} := by
    change embStk familyCouplingSourceReg {S with R := Function.update S.R (familyCouplingSourceReg 132) output} = _
    rw [embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective]
  have hproj : embStk familyCouplingSourceReg G = H := embStk_ovr familyCouplingSourceReg_injective H T
  have hoff (k : Fin 144) (hk : k ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94]) :
      H.R k = (embStk familyCouplingSourceReg T).R k :=
    couplingHeadersR_off (2^15*p) q s t u band a b _ k hk
  have hcacheG : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg G) := by
    apply hcache.of_frame
    intro i
    have hh := (embOvr_off (e := familyCouplingSourceReg) H.get T (fun j he =>
      couplingCacheLegacyReg_off recovery i (couplingLegacyReg j) (familyInverseLegacyReg_injective he))).2
    have hne : familyInverseLegacyReg (couplingCachePort recovery i) ≠ (132 : Fin 263) := by
      intro he
      have hv := congrArg (fun k : Fin 263 => k.val) he
      have hg := couplingCachePort_ge recovery i
      dsimp [familyInverseLegacyReg] at hv
      omega
    exact hh.trans (Function.update_of_ne hne _ _)
  obtain ⟨vi,n₂,hui,hn₂,hei,hfield,hlen,hRnorm,hpoint⟩ := placedCachedFeedCouplingPass_spec
    (body := fun p : Empty => nomatch p) recovery hQ false hA hp hst hαu hθ hgap hbudget hrowWidth has hbs hband rfl D C x
    (fun i => (value q (C i)).re) K (1/(2 : ℝ)^target) 0 (by positivity) hcount hC
    (by intro i _; exact hDnorm i) (by intro i hi; simpa only [Bool.false_eq_true,ite_false,Real.norm_eq_abs] using hDerror i hi)
    hmass (by intro i; simp [q]) borrowed (S.R 132) pageTail (embDn familyInverseLegacyReg v₁) (embStk familyInverseLegacyReg G) hcoupling hcacheG
    (by change (embStk familyCouplingSourceReg G).R 107 = []; rw [hproj,hoff 107 (by decide)];
        rw [hT]; simpa using hready.blank 107 (by decide) (by decide) (by decide))
    (by change (embStk familyCouplingSourceReg G).R 132 = _; rw [hproj,hoff 132 (by decide)]; rw [hT]; simp [output,w])
    (by change (embStk familyCouplingSourceReg G).R 143 = []; rw [hproj,hoff 143 (by decide)]; rw [hT]; simpa using h143)
    (by change (embStk familyCouplingSourceReg G).R 131 = []; rw [hproj,hoff 131 (by decide)]; rw [hT]; simpa using hready.fresh 131 (by simp))
    (by change (embStk familyCouplingSourceReg G).R 134 = []; rw [hproj,hoff 134 (by decide)]; rw [hT]; simpa using hready.fresh 134 (by simp))
    (by change (embStk familyCouplingSourceReg G).R 135 = []; rw [hproj,hoff 135 (by decide)]; rw [hT]; simpa using hready.fresh 135 (by simp))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) hei v₁ rfl G rfl
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  have he₂' : Exec body (embProg familyInverseLegacyReg Empty.elim (placedCachedFeedCouplingPass (P₀ := Empty) recovery hQ false))
      (mk v₁ G) n₂ (mk v₂ {G with R := Function.update G.R 110 (cstream A w (chirpLine s R)++G.R 110)}) := by
    refine he₂.cast rfl ?_
    apply congrArg (mk v₂)
    rw [embOvr_updR familyInverseLegacyReg_injective,embOvr_stk,hfield]
    rfl
  have hfit : ∀ i, Fits w (R i) := fun i => fits_of_value_power hrowWidth _ (hRnorm i)
  have hw : 0 < w := by dsimp [w,executionWidth]; omega
  refine ⟨v₂,n₁+n₂,D,hu₂.trans (hui.trans hu₁),Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂',hDnorm,hDerror,hRnorm,?_⟩
  intro i hi
  have hh := hpoint i.val i.val_lt (Or.inr (by simpa using hi))
  rw [hfield] at hh
  have hread := publishedCellRead_encodedField (q := q) (by omega : 4 ≤ A) hw R (G.R 110) hfit i
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero] at hread
  simp only [Bool.false_eq_true,ite_false] at hh
  change |(value q (decodeWord (((cstream A w (chirpLine s R)++G.R 110).drop (i.val*w)).take w))).re - _| ≤ _ at hh
  rw [hread] at hh
  simpa only [ZMod.natCast_zmod_val,add_zero,q,w,band,e] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
