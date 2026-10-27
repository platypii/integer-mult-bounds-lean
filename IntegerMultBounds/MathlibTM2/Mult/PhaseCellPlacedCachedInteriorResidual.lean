module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInteriorForCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedFeedCouplingPass

/-! Execute the interior solve and its boundary-residual row pass with derived input bounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  .seq (placedInteriorForCoupling hR hQ) (placedCachedFeedCouplingPass recovery hQ false)

def placedCachedInteriorResidualCost (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  interiorForCouplingCost p l s t u target rhsExp a b+
    placedCachedFeedCouplingPassCost false (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t (PhaseCellBand.width p u) a b
      (couplingCoefficientPage (2^15*p) (executionPrecision p l target rhsExp)
        s t u (PhaseCellBand.width p u) a b s).length

theorem placedCachedInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 256 Q A U) (S : Stacks 256 A) (borrowed outputTail pageTail : List (Fin (A+4)))
    (E₀ : ZMod s → GaussianInt)
    (hE₀ : ∀ k, ‖value (executionPrecision p l target rhsExp) (E₀ k)‖ ≤
      (2 : ℝ)^interiorOutputExponent p l target rhsExp)
    (hdst : (embStk couplingSourceReg S).R 132 = cstream A (executionWidth p l target rhsExp) (chirpLine s E₀)++outputTail)
    (h127 : (embStk couplingSourceReg S).R 127 = []) (h138 : (embStk couplingSourceReg S).R 138 = [])
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a) (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk couplingSourceReg S))
    (h143 : (embStk couplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b pageTail S)
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
    let T := embStk couplingSourceReg S
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
      let T' : Stacks 144 A := {T with R := (couplingHeadersR (2^15*p) q s t u band a b
        (Function.update T.R 132 (cstream A w (chirpLine s D)++outputTail)))}
      let G := embOvr couplingSourceReg T'.get S
      v'.user = v.user ∧ n ≤ placedCachedInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec body (placedCachedInteriorResidual recovery hR hQ) (mk v S) n
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
  let T := embStk couplingSourceReg S
  obtain ⟨v₁,n₁,D,hu₁,hn₁,he₁,hcoupling,hDnorm,hDerror⟩ := placedInteriorForCoupling_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S
    borrowed outputTail E₀ hE₀ hdst h127 h138 haMaster hbMaster hready
  let base := Function.update T.R 132 (cstream A w (chirpLine s D)++outputTail)
  let T' : Stacks 144 A := {T with R := couplingHeadersR (2^15*p) q s t u band a b base}
  let G := embOvr couplingSourceReg T'.get S
  have hproj : embStk couplingSourceReg G = T' := embStk_ovr couplingSourceReg_injective T' S
  have hoff (k : Fin 144) (hk : k ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94]) : T'.R k = base k :=
    couplingHeadersR_off (2^15*p) q s t u band a b base k hk
  have hcacheG : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail G := by
    apply hcache.of_frame
    intro i
    exact (embOvr_off (e := couplingSourceReg) T'.get S (fun j =>
      couplingCacheLegacyReg_off recovery i (couplingLegacyReg j))).2
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hfield,hlen,hRnorm,hpoint⟩ := placedCachedFeedCouplingPass_spec (body := body)
    recovery hQ false hA hp hst hαu hθ hgap hbudget hrowWidth has hbs hband rfl D C x
    (fun i => (value q (C i)).re) K (1/(2 : ℝ)^target) 0 (by positivity) hcount hC
    (by intro i _; exact hDnorm i) (by intro i hi; simpa only [Bool.false_eq_true,ite_false,Real.norm_eq_abs] using hDerror i hi)
    hmass (by intro i; simp [q]) borrowed outputTail pageTail v₁ G hcoupling hcacheG
    (by change (embStk couplingSourceReg G).R 107 = []; rw [hproj,hoff 107 (by decide)];
        simpa [base] using hready.blank 107 (by decide) (by decide) (by decide))
    (by change (embStk couplingSourceReg G).R 132 = _; rw [hproj,hoff 132 (by decide)]; simp [base,w])
    (by change (embStk couplingSourceReg G).R 143 = []; rw [hproj,hoff 143 (by decide)]; simpa [base] using h143)
    (by change (embStk couplingSourceReg G).R 131 = []; rw [hproj,hoff 131 (by decide)]; simpa [base] using hready.fresh 131 (by simp))
    (by change (embStk couplingSourceReg G).R 134 = []; rw [hproj,hoff 134 (by decide)]; simpa [base] using hready.fresh 134 (by simp))
    (by change (embStk couplingSourceReg G).R 135 = []; rw [hproj,hoff 135 (by decide)]; simpa [base] using hready.fresh 135 (by simp))
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  have hfit : ∀ i, Fits w (R i) := fun i => fits_of_value_power hrowWidth _ (hRnorm i)
  have hw : 0 < w := by dsimp [w,executionWidth]; omega
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_,hDnorm,hDerror,hRnorm,?_⟩
  · exact Nat.add_le_add hn₁ hn₂
  · apply congrArg (mk v₂)
    rw [hfield]
  · intro i hi
    have hh := hpoint i.val i.val_lt (Or.inr (by simpa using hi))
    rw [hfield] at hh
    have hread := publishedCellRead_encodedField (q := q) (by omega : 4 ≤ A) hw R (G.R 110) hfit i
    simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero] at hread
    simp only [Bool.false_eq_true,ite_false] at hh
    rw [hread] at hh
    simpa only [ZMod.natCast_zmod_val,add_zero,q,w,band,e] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
