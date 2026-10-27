module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingFieldError

/-! A residual or recovery pass from ordinary retained masters, restoring its runtime headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def restoredCouplingPass (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  .seq installCouplingHeaders (.seq (feedCouplingPass hQ boundary) releaseCouplingHeaders)

def restoredCouplingPassCost (boundary : Bool) (P q s t u band a b : ℕ) : ℕ :=
  installCouplingHeadersCost P q s t u band a b+
    (feedCouplingPassCost boundary P q (2*q+8) s t u band a b+
      releaseCouplingHeadersCost P q s t u band a b)

theorem restoredCouplingPass_spec (hQ : SS.states ≤ Q)
    {p q N l s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ 2*q+8)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C i)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ i ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C i)).re-x i| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ i, |(value q (B i)).re-b₀ i| ≤ rhsError)
    (tail sourceTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s B)++tail) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s C)++sourceTail)
    (h143 : S.R 143 = []) :
    let R := couplingRowField (2^15*p) q t u band a b boundary C B
    ∃ v' n, v'.user = v.user ∧ n ≤ restoredCouplingPassCost boundary (2^15*p) q s t u band a b ∧
      Exec (embTab groupReg body) (restoredCouplingPass hQ boundary) (mk v S) n
        (mk v' {S with R := Function.update S.R 110 (cstream A (2*q+8) (chirpLine s R)++S.R 110)}) ∧
      LengthKeyReady (2^15*p) N q l s t u band 0 0
        (cstream A (2*q+8) (chirpLine s R)++S.R 110)
        {S with R := Function.update S.R 110 (cstream A (2*q+8) (chirpLine s R)++S.R 110)} ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp) ∧
      ∀ i, |(value q (R i)).re-(b₀ i-SchurDominance.couple (realMatrix s t p u)
        (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  obtain ⟨v₁,hu₁,he₁,hcoupling⟩ := installCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) N q l s t u band a b (cstream A (2*q+8) (chirpLine s B)++tail)
    v S hready haMaster hbMaster
  let S₁ : Stacks 144 A := {S with R := couplingHeadersR (2^15*p) q s t u band a b S.R}
  have hoff (k : Fin 144) (hk : k ∉ couplingHeaderRegisters) : S₁.R k = S.R k :=
    couplingHeadersR_off (2^15*p) q s t u band a b S.R k hk
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hfield,hlen,hnorm,herror⟩ := feedCouplingPass_spec (body := body)
    hQ boundary hA hp hst hαu hθ hgap hbudget hw haS hbS hbandS hband C B x b₀ K ε rhsError hε
    hcount hB hC hx hmass hBError tail sourceTail v₁ S₁ hcoupling
    (by rw [hoff 107 (by decide)]; exact hready.blank 107 (by decide) (by decide) (by decide))
    (by rw [hoff 132 (by decide)]; exact hsource)
    (by rw [hoff 143 (by decide)]; exact h143)
    (by rw [hoff 131 (by decide)]; exact hready.fresh 131 (by simp))
    (by rw [hoff 134 (by decide)]; exact hready.fresh 134 (by simp))
    (by rw [hoff 135 (by decide)]; exact hready.fresh 135 (by simp))
  let R := couplingRowField (2^15*p) q t u band a b boundary C B
  let S₂ : Stacks 144 A := {S with R := (Function.update S.R 110
    (cstream A (2*q+8) (chirpLine s R)++S.R 110))}
  have hready₂ : LengthKeyReady (2^15*p) N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s R)++S.R 110) S₂ := hready.update_source _
  have hblank : ∀ k ∈ couplingHeaderRegisters, S₂.R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    exact hready₂.blank k hk117 hk93 hk110
  obtain ⟨v₃,hu₃,he₃⟩ := releaseCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) q s t u band a b v₂ S₂ hblank
  have he₂' : Exec (embTab groupReg body) (feedCouplingPass hQ boundary) (mk v₁ S₁) n₂
      (mk v₂ {S₂ with R := couplingHeadersR (2^15*p) q s t u band a b S₂.R}) := by
    rw [hfield] at he₂
    convert he₂ using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    change couplingHeadersR (2^15*p) q s t u band a b (Function.update S.R 110
      (cstream A (2*q+8) (chirpLine s R)++S.R 110)) = _
    rw [couplingHeadersR_update (2^15*p) q s t u band a b S.R 110 _ (by decide)]
    rw [hoff 110 (by decide)]
  refine ⟨v₃,installCouplingHeadersCost (2^15*p) q s t u band a b+
    (n₂+releaseCouplingHeadersCost (2^15*p) q s t u band a b),hu₃.trans (hu₂.trans hu₁),
    ?_,Exec.seq he₁ (Exec.seq he₂' he₃),hready₂,hnorm,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _
  · subst band
    exact couplingRowField_error boundary hA hp hst hαu hθ hgap hbudget hw C B x b₀ K ε rhsError
      hε hcount hB hC hx hmass hBError

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
