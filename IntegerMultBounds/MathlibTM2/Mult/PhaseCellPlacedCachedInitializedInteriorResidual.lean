module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls
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

noncomputable def placedCachedInitializedInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  .seq placedInteriorOutputInitialize (placedCachedInteriorResidual recovery hR hQ)

def placedCachedInitializedInteriorResidualCost (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  initializeInteriorOutputCost (executionPrecision p l target rhsExp) s+
    placedCachedInteriorResidualCost p l s t u target rhsExp a b

theorem placedCachedInitializedInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 256 Q A U) (S : Stacks 256 A) (borrowed pageTail : List (Fin (A+4)))
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
        (Function.update T.R 132 (cstream A w (chirpLine s D)++S.R 132)))}
      let G := embOvr couplingSourceReg T'.get S
      v'.user = v.user ∧ n ≤ placedCachedInitializedInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec body (placedCachedInitializedInteriorResidual recovery hR hQ) (mk v S) n
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
  let raw := cstream A w (chirpLine s C)
  let T := embStk couplingSourceReg S
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 132 (raw++S.R 132)}
  have hproj : embStk couplingSourceReg S₁ = {T with R := Function.update T.R 132 (raw++S.R 132)} :=
    embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S 132 _
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hq : (S.R 119).length = q := by
    change ((embStk couplingSourceReg S).R 119).length = q
    simpa [T,groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    change ((embStk couplingSourceReg S).R 121).length = s
    simpa [T,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedInteriorOutputInitialize_exec (body := body)
    q s raw borrowed v S hq hs hready.source (by simp [raw,hw])
    (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  have hC' : ∀ k, ‖value q (C k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro k
    exact (hC k).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (rhsExponent_le_interiorOutputExponent p l target rhsExp))
  have hcache₁ : CouplingPageCacheReady recovery (2^15*p) q w s t u (PhaseCellBand.width p u) a b pageTail S₁ := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne : couplingCachePort recovery i ≠ (132 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    simp [S₁,hne]
  obtain ⟨v₂,n₂,D,hu₂,hn₂,he₂,hDnorm,hDerror,hnorm,herror⟩ := placedCachedInteriorResidual_spec (body := body)
    recovery hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v₁ S₁
    borrowed (S.R 132) pageTail C hC' (by change S₁.R 132 = _; rfl)
    (by rw [hproj]; simpa using h127) (by rw [hproj]; simpa using h138)
    (by rw [hproj]; simpa using haMaster) (by rw [hproj]; simpa using hbMaster)
    (by rw [hproj]; exact hready.update_output (raw++S.R 132))
    (by rw [hproj]; simpa using h143) hcache₁ hcount hrowWidth K hmass
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,hDnorm,hDerror,hnorm,herror⟩
  apply congrArg (mk v₂)
  simp only [hproj,Function.update_idem]
  have hov (X : Stacks 144 A) : embOvr couplingSourceReg X.get S₁ = embOvr couplingSourceReg X.get S :=
    embOvr_updateR_base couplingSourceReg couplingSourceReg_injective X S 132 _
  rw [hov]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
