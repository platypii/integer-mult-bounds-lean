module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! The owned interior and residual lines with all private coupling headers released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def restoredInteriorResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (initializedInteriorResidual hR hQ) releaseCouplingHeaders

def restoredInteriorResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  initializedInteriorResidualCost p l s t u target rhsExp a b+
    releaseCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp)
      s t u (PhaseCellBand.width p u) a b

theorem restoredInteriorResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S)
    (h143 : S.R 143 = [])
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
      let R := couplingRowField (2^15*p) q t u band a b false D C
      v'.user = v.user ∧ n ≤ restoredInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (restoredInteriorResidual hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
          110 (cstream A w (chirpLine s R)++S.R 110))}) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp e (8*p+1) countExp) ∧
      ∀ i, |(value q (R i)).re-((value q (C i)).re-
        SchurDominance.couple (realMatrix s t p u) (haloInterior s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^e*(1/(2 : ℝ)^q))+K*(1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  obtain ⟨v₁,n,D,hu₁,hn,he₁,hDnorm,hDerror,hnorm,herror⟩ := initializedInteriorResidual_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S borrowed
    h127 h138 haMaster hbMaster hready h143 hcount hrowWidth K hmass
  let R := couplingRowField (2^15*p) q t u band a b false D C
  let S₁ : Stacks 144 A := {S with R := (Function.update
    (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
    110 (cstream A w (chirpLine s R)++S.R 110))}
  have hblank : ∀ k ∈ couplingHeaderRegisters, S₁.R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk132 : k ≠ 132 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    simpa [S₁,hk110,hk132] using hready.blank k hk117 hk93 hk110
  obtain ⟨v₂,hu₂,he₂⟩ := releaseCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) q s t u band a b v₁ S₁ hblank
  have he₁' : Exec (embTab groupReg body) (initializedInteriorResidual hR hQ) (mk v S) n
      (mk v₁ {S₁ with R := couplingHeadersR (2^15*p) q s t u band a b S₁.R}) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    change couplingHeadersR (2^15*p) q s t u band a b
      (Function.update (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132))
        110 (cstream A w (chirpLine s R)++S.R 110)) = _
    exact couplingHeadersR_update (2^15*p) q s t u band a b _ 110 _ (by decide)
  refine ⟨v₂,n+releaseCouplingHeadersCost (2^15*p) q s t u band a b,D,hu₂.trans hu₁,
    Nat.add_le_add_right hn _,Exec.seq he₁' he₂,hDnorm,hDerror,hnorm,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
