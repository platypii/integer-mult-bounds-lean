module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedFeedCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingFieldError

/-! A residual or recovery pass from ordinary retained masters, restoring its runtime headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedRestoredCouplingPass (recovery : Bool) (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 256 Q A U :=
  .seq placedCouplingHeadersInstall (.seq (placedCachedFeedCouplingPass recovery hQ boundary) placedCouplingHeadersRelease)

def placedCachedRestoredCouplingPassCost (boundary : Bool) (P q s t u band a b Nwords : ℕ) : ℕ :=
  installCouplingHeadersCost P q s t u band a b+
    (placedCachedFeedCouplingPassCost boundary q (2*q+8) s t band a b Nwords+
      releaseCouplingHeadersCost P q s t u band a b)

theorem placedCachedRestoredCouplingPass_spec (recovery : Bool) (hQ : SS.states ≤ Q)
    {p q N l s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ 2*q+8)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ (if true then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C i)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ i ∈ (if true then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C i)).re-x i| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ i, |(value q (B i)).re-b₀ i| ≤ rhsError)
    (tail sourceTail pageTail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s B)++tail) (embStk couplingSourceReg S))
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a) (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (hsource : (embStk couplingSourceReg S).R 132 = cstream A (2*q+8) (chirpLine s C)++sourceTail)
    (h143 : (embStk couplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p) q (2*q+8) s t u band a b pageTail S) :
      let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, v'.user = v.user ∧ n ≤ placedCachedRestoredCouplingPassCost true (2^15*p) q s t u band a b
      (couplingCoefficientPage (2^15*p) q s t u band a b s).length ∧
      Exec body (placedCachedRestoredCouplingPass recovery hQ true) (mk v S) n
        (mk v' {S with R := Function.update S.R 110 (cstream A (2*q+8) (chirpLine s R)++S.R 110)}) ∧
      LengthKeyReady (2^15*p) N q l s t u band 0 0
        (cstream A (2*q+8) (chirpLine s R)++S.R 110)
        (embStk couplingSourceReg {S with R := Function.update S.R 110 (cstream A (2*q+8) (chirpLine s R)++S.R 110)}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp) ∧
      ∀ i, |(value q (R i)).re-(b₀ i-SchurDominance.couple (realMatrix s t p u)
        (if true then haloBoundary s t band a b else haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  let T := embStk couplingSourceReg S
  let H : Stacks 144 A := {T with R := couplingHeadersR (2^15*p) q s t u band a b T.R}
  let G := embOvr couplingSourceReg H.get S
  have hprojG : embStk couplingSourceReg G = H := embStk_ovr couplingSourceReg_injective H S
  obtain ⟨v₁,hu₁,he₁,hcoupling⟩ := placedCouplingHeadersInstall_exec (body := body)
    (2^15*p) N q l s t u band a b (cstream A (2*q+8) (chirpLine s B)++tail)
    v S hready haMaster hbMaster
  have hoff (k : Fin 144) (hk : k ∉ couplingHeaderRegisters) : H.R k = T.R k :=
    couplingHeadersR_off (2^15*p) q s t u band a b T.R k hk
  have hcacheG : CouplingPageCacheReady recovery (2^15*p) q (2*q+8) s t u band a b pageTail G := by
    apply hcache.of_frame
    intro i
    exact (embOvr_off (e := couplingSourceReg) H.get S (fun j =>
      couplingCacheLegacyReg_off recovery i (couplingLegacyReg j))).2
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hfield,hlen,hnorm,herror⟩ := placedCachedFeedCouplingPass_spec (body := body)
    recovery hQ true hA hp hst hαu hθ hgap hbudget hw haS hbS hbandS hband C B x b₀ K ε rhsError hε
    hcount hB hC hx hmass hBError tail sourceTail pageTail v₁ G hcoupling hcacheG
    (by change (embStk couplingSourceReg G).R 107 = []; rw [hprojG,hoff 107 (by decide)]; exact hready.blank 107 (by decide) (by decide) (by decide))
    (by change (embStk couplingSourceReg G).R 132 = _; rw [hprojG,hoff 132 (by decide)]; exact hsource)
    (by change (embStk couplingSourceReg G).R 143 = []; rw [hprojG,hoff 143 (by decide)]; exact h143)
    (by change (embStk couplingSourceReg G).R 131 = []; rw [hprojG,hoff 131 (by decide)]; exact hready.fresh 131 (by simp))
    (by change (embStk couplingSourceReg G).R 134 = []; rw [hprojG,hoff 134 (by decide)]; exact hready.fresh 134 (by simp))
    (by change (embStk couplingSourceReg G).R 135 = []; rw [hprojG,hoff 135 (by decide)]; exact hready.fresh 135 (by simp))
  have hsame : guardedCouplingRowField (2^15*p) q t u band a b true C B =
      couplingRowField (2^15*p) q t u band a b true C B := by
    funext i
    exact guardedCouplingRowField_eq hst (2^15*p) q u band a b true hbS C B i (Or.inl rfl)
  rw [hsame] at hfield hnorm
  let R := couplingRowField (2^15*p) q t u band a b true C B
  let input := cstream A (2*q+8) (chirpLine s R)++S.R 110
  let S₂ : Stacks 256 A := {S with R := Function.update S.R 110 input}
  have hproj₂ : embStk couplingSourceReg S₂ = {T with R := Function.update T.R 110 input} :=
    embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S 110 input
  have hready₂ : LengthKeyReady (2^15*p) N q l s t u band 0 0 input
      (embStk couplingSourceReg S₂) := by
    rw [hproj₂]; exact hready.update_source input
  have hblank : ∀ k ∈ couplingHeaderRegisters, (embStk couplingSourceReg S₂).R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    exact hready₂.blank k hk117 hk93 hk110
  obtain ⟨v₃,hu₃,he₃⟩ := placedCouplingHeadersRelease_exec (body := body)
    (2^15*p) q s t u band a b v₂ S₂ hblank
  have hG110 : G.R 110 = S.R 110 := by
    change (embStk couplingSourceReg G).R 110 = _
    rw [hprojG,hoff 110 (by decide)]; rfl
  have hpre : embOvr couplingSourceReg
      ({embStk couplingSourceReg S₂ with R := (couplingHeadersR (2^15*p) q s t u band a b
        (embStk couplingSourceReg S₂).R)} : Stacks 144 A).get S₂ =
      {G with R := Function.update G.R 110 input} := by
    rw [hproj₂,couplingHeadersR_update _ _ _ _ _ _ _ _ _ 110 _ (by decide)]
    have hbase (X : Stacks 144 A) : embOvr couplingSourceReg X.get S₂ = embOvr couplingSourceReg X.get S :=
      embOvr_updateR_base couplingSourceReg couplingSourceReg_injective X S 110 input
    rw [hbase]
    change embOvr couplingSourceReg ({H with R := Function.update H.R 110 input} : Stacks 144 A).get S = _
    rw [embOvr_updR couplingSourceReg_injective]; rfl
  have he₂' : Exec body (placedCachedFeedCouplingPass recovery hQ true) (mk v₁ G) n₂
      (mk v₂ {G with R := Function.update G.R 110 input}) := by
    rw [hfield] at he₂
    simpa only [hG110] using he₂
  have he₃' : Exec body placedCouplingHeadersRelease
      (mk v₂ {G with R := Function.update G.R 110 input})
      (releaseCouplingHeadersCost (2^15*p) q s t u band a b) (mk v₃ S₂) := by
    simpa only [hpre] using he₃
  refine ⟨v₃,installCouplingHeadersCost (2^15*p) q s t u band a b+
    (n₂+releaseCouplingHeadersCost (2^15*p) q s t u band a b),hu₃.trans (hu₂.trans hu₁),
    ?_,Exec.seq he₁ (Exec.seq he₂' he₃'),hready₂,hnorm,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _
  · subst band
    exact couplingRowField_error true hA hp hst hαu hθ hgap hbudget hw C B x b₀ K ε rhsError
      hε hcount hB hC hx hmass hBError

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
