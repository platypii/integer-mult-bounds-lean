module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! Complete the first inverse interior/residual stage and release its private
coupling headers. The exact caller frame retains all numerical caches. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyCouplingHeadersRelease : Pr P₀ 263 Q A U :=
  embProg familyCouplingSourceReg Empty.elim (releaseCouplingHeaders (P₀ := Empty))

theorem familyCouplingHeadersRelease_exec (P q s t u band a b : ℕ)
    (v : HS 263 Q A U) (S : Stacks 263 A)
    (hblank : ∀ k ∈ couplingHeaderRegisters, (embStk familyCouplingSourceReg S).R k = []) :
    let H : Stacks 144 A := {embStk familyCouplingSourceReg S with R :=
      (couplingHeadersR P q s t u band a b (embStk familyCouplingSourceReg S).R)}
    ∃ v', v'.user = v.user ∧ Exec body familyCouplingHeadersRelease
      (mk v (embOvr familyCouplingSourceReg H.get S))
      (releaseCouplingHeadersCost P q s t u band a b) (mk v' S) := by
  dsimp only
  let T := embStk familyCouplingSourceReg S
  let H : Stacks 144 A := {T with R := couplingHeadersR P q s t u band a b T.R}
  let G := embOvr familyCouplingSourceReg H.get S
  obtain ⟨vi,hu,he⟩ := releaseCouplingHeaders_exec (body := fun p : Empty => nomatch p)
    P q s t u band a b (embDn familyCouplingSourceReg v) T hblank
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyCouplingSourceReg_injective (fun p => nomatch p) he v rfl G (embStk_ovr familyCouplingSourceReg_injective H S)
  refine ⟨v',hu'.trans hu,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [show G = embOvr familyCouplingSourceReg H.get S from rfl,embOvr_overwrite,embOvr_stk]

noncomputable def familyRestoredInteriorResidual (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 263 Q A U :=
  .seq (familyInteriorResidual recovery hR hQ) familyCouplingHeadersRelease

def familyRestoredInteriorResidualCost (A p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  familyInteriorResidualCost A p l s t u target rhsExp a b+
    releaseCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) a b

theorem familyRestoredInteriorResidual_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      v'.user = v.user ∧ n ≤ familyRestoredInteriorResidualCost A p l s t u target rhsExp a b ∧
      Exec body (familyRestoredInteriorResidual recovery hR hQ) (mk v S) n
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
  obtain ⟨v₁,n,D,hu₁,hn,he₁,hDnorm,hDerror,hnorm,herror⟩ := familyInteriorResidual_spec (body := body)
    recovery hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S borrowed pageTail familyTail
    h127 h138 haMaster hbMaster hready h143 hcache hfamily hfamilyFresh hcount hrowWidth K hmass
  let R := guardedCouplingRowField (2^15*p) q t u band a b false D C
  let output := cstream A w (chirpLine s D)++S.R 132
  let input := cstream A w (chirpLine s R)++S.R 110
  let T : Stacks 263 A := {S with R := Function.update S.R 132 output}
  let H : Stacks 144 A := {embStk familyCouplingSourceReg T with R := couplingHeadersR (2^15*p) q s t u band a b (embStk familyCouplingSourceReg T).R}
  let G := embOvr familyCouplingSourceReg H.get T
  let S₁ : Stacks 263 A := {S with R := (Function.update (Function.update S.R 132 output) 110 input)}
  have hT : embStk familyCouplingSourceReg T =
      {embStk familyCouplingSourceReg S with R := Function.update (embStk familyCouplingSourceReg S).R 132 output} := by
    change embStk familyCouplingSourceReg {S with R := Function.update S.R (familyCouplingSourceReg 132) output} = _
    rw [embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective]
  have hproj : embStk familyCouplingSourceReg S₁ =
      {embStk familyCouplingSourceReg T with R := Function.update (embStk familyCouplingSourceReg T).R 110 input} := by
    change embStk familyCouplingSourceReg {T with R := Function.update T.R (familyCouplingSourceReg 110) input} = _
    rw [embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective]
  have hblank : ∀ k ∈ couplingHeaderRegisters, (embStk familyCouplingSourceReg S₁).R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk132 : k ≠ 132 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    rw [hproj,hT]
    simpa [hk110,hk132] using hready.blank k hk117 hk93 hk110
  obtain ⟨v₂,hu₂,he₂⟩ := familyCouplingHeadersRelease_exec (body := body) (2^15*p) q s t u band a b v₁ S₁ hblank
  have hG110 : G.R 110 = S.R 110 := by
    change (embStk familyCouplingSourceReg G).R 110 = _
    rw [embStk_ovr familyCouplingSourceReg_injective H T]
    dsimp only [H]
    rw [couplingHeadersR_off _ _ _ _ _ _ _ _ _ 110 (by decide)]
    rfl
  have hpre : embOvr familyCouplingSourceReg
      ({embStk familyCouplingSourceReg S₁ with R := (couplingHeadersR (2^15*p) q s t u band a b
        (embStk familyCouplingSourceReg S₁).R)} : Stacks 144 A).get S₁ =
      {G with R := Function.update G.R 110 input} := by
    rw [hproj,couplingHeadersR_update _ _ _ _ _ _ _ _ _ 110 _ (by decide)]
    have hbase (X : Stacks 144 A) : embOvr familyCouplingSourceReg X.get S₁ = embOvr familyCouplingSourceReg X.get T :=
      embOvr_updateR_base familyCouplingSourceReg familyCouplingSourceReg_injective X T 110 input
    rw [hbase]
    change embOvr familyCouplingSourceReg ({H with R := Function.update H.R 110 input} : Stacks 144 A).get T = _
    rw [embOvr_updR familyCouplingSourceReg_injective]
    rfl
  have he₁' : Exec body (familyInteriorResidual recovery hR hQ) (mk v S) n
      (mk v₁ {G with R := Function.update G.R 110 input}) := by
    change Exec body (familyInteriorResidual recovery hR hQ) (mk v S) n
      (mk v₁ {G with R := Function.update G.R 110 (cstream A w (chirpLine s R)++G.R 110)}) at he₁
    simpa only [hG110] using he₁
  have he₂' : Exec body familyCouplingHeadersRelease (mk v₁ {G with R := Function.update G.R 110 input})
      (releaseCouplingHeadersCost (2^15*p) q s t u band a b) (mk v₂ S₁) := by
    simpa only [hpre] using he₂
  exact ⟨v₂,n+releaseCouplingHeadersCost (2^15*p) q s t u band a b,D,hu₂.trans hu₁,
    Nat.add_le_add_right hn _,Exec.seq he₁' he₂',hDnorm,hDerror,hnorm,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
