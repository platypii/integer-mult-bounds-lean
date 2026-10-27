module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedInitializedInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! The owned interior and residual lines with all private coupling headers released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedRestoredInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  .seq (placedCachedInitializedInteriorResidual recovery hR hQ) placedCouplingHeadersRelease

def placedCachedRestoredInteriorResidualCost (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  placedCachedInitializedInteriorResidualCost p l s t u target rhsExp a b+
    releaseCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp)
      s t u (PhaseCellBand.width p u) a b

theorem placedCachedRestoredInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
      v'.user = v.user ∧ n ≤ placedCachedRestoredInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec body (placedCachedRestoredInteriorResidual recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
          110 (cstream A w (chirpLine s R)++S.R 110))}) ∧
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
  let T := embStk couplingSourceReg S
  obtain ⟨v₁,n,D,hu₁,hn,he₁,hDnorm,hDerror,hnorm,herror⟩ := placedCachedInitializedInteriorResidual_spec (body := body)
    recovery hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S borrowed pageTail
    h127 h138 haMaster hbMaster hready h143 hcache hcount hrowWidth K hmass
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  let output := cstream A w (chirpLine s D)++S.R 132
  let input := cstream A w (chirpLine s R)++S.R 110
  let T₁ : Stacks 144 A := {T with R := Function.update T.R 132 output}
  let H : Stacks 144 A := {T₁ with R := couplingHeadersR (2^15*p) q s t u band a b T₁.R}
  let G := embOvr couplingSourceReg H.get S
  let S₁ : Stacks 256 A := {S with R := (Function.update (Function.update S.R 132 output) 110 input)}
  have hproj : embStk couplingSourceReg S₁ =
      {T₁ with R := Function.update T₁.R 110 input} := by
    let V : Stacks 256 A := {S with R := Function.update S.R 132 output}
    change embStk couplingSourceReg {V with R := Function.update V.R (couplingSourceReg 110) input} = _
    rw [embStk_updateR_inner couplingSourceReg couplingSourceReg_injective]
    dsimp only [V]
    have h132 : embStk couplingSourceReg {S with R := Function.update S.R 132 output} = T₁ :=
      embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S 132 output
    rw [h132]
  have hblank : ∀ k ∈ couplingHeaderRegisters, (embStk couplingSourceReg S₁).R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk132 : k ≠ 132 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    rw [hproj]
    simpa [T₁,hk110,hk132] using hready.blank k hk117 hk93 hk110
  obtain ⟨v₂,hu₂,he₂⟩ := placedCouplingHeadersRelease_exec (body := body)
    (2^15*p) q s t u band a b v₁ S₁ hblank
  have hG110 : G.R 110 = S.R 110 := by
    change (embStk couplingSourceReg G).R 110 = _
    rw [embStk_ovr couplingSourceReg_injective H S]
    dsimp only [H]
    rw [couplingHeadersR_off _ _ _ _ _ _ _ _ _ 110 (by decide)]
    rfl
  have hpre : (embOvr couplingSourceReg
      ({embStk couplingSourceReg S₁ with R := (couplingHeadersR (2^15*p) q s t u band a b
        (embStk couplingSourceReg S₁).R)} : Stacks 144 A).get S₁) =
      {G with R := Function.update G.R 110 input} := by
    rw [hproj,couplingHeadersR_update _ _ _ _ _ _ _ _ _ 110 _ (by decide)]
    have hbase (X : Stacks 144 A) : embOvr couplingSourceReg X.get S₁ = embOvr couplingSourceReg X.get S := by
      let V : Stacks 256 A := {S with R := Function.update S.R 132 output}
      change embOvr couplingSourceReg X.get {V with R := Function.update V.R (couplingSourceReg 110) input} = _
      rw [embOvr_updateR_base couplingSourceReg couplingSourceReg_injective]
      exact embOvr_updateR_base couplingSourceReg couplingSourceReg_injective X S 132 output
    rw [hbase]
    change embOvr couplingSourceReg ({H with R := Function.update H.R 110 input} : Stacks 144 A).get S = _
    rw [embOvr_updR couplingSourceReg_injective]
    rfl
  have he₁' : Exec body (placedCachedInitializedInteriorResidual recovery hR hQ) (mk v S) n
      (mk v₁ {G with R := Function.update G.R 110 input}) := by
    change Exec body (placedCachedInitializedInteriorResidual recovery hR hQ) (mk v S) n
      (mk v₁ {G with R := Function.update G.R 110 (cstream A w (chirpLine s R)++G.R 110)}) at he₁
    simpa only [hG110] using he₁
  have he₂' : Exec body placedCouplingHeadersRelease
      (mk v₁ {G with R := Function.update G.R 110 input})
      (releaseCouplingHeadersCost (2^15*p) q s t u band a b) (mk v₂ S₁) := by
    simpa only [hpre] using he₂
  exact ⟨v₂,n+releaseCouplingHeadersCost (2^15*p) q s t u band a b,D,hu₂.trans hu₁,
    Nat.add_le_add_right hn _,Exec.seq he₁' he₂',hDnorm,hDerror,hnorm,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
