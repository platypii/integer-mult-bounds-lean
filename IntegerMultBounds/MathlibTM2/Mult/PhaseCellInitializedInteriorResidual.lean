module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput

/-! Allocate the ambient output from the actual RHS, then solve and form the residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedInteriorResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq initializeInteriorOutput (interiorResidual hR hQ)

def initializedInteriorResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  initializeInteriorOutputCost (executionPrecision p l target rhsExp) s+
    interiorResidualCost p l s t u target rhsExp a b

theorem initializedInteriorResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      v'.user = v.user ∧ n ≤ initializedInteriorResidualCost p l s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (initializedInteriorResidual hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (couplingHeadersR (2^15*p) q s t u band a b
            (Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132)))
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
  let raw := cstream A w (chirpLine s C)
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 132 (raw++S.R 132)}
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hq : (S.R 119).length = q := by
    simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeInteriorOutput_exec
    (body := embTab groupReg body) q s raw borrowed v S hq hs hready.source
    (by simp [raw,hw]) (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  have hC' : ∀ k, ‖value q (C k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro k
    exact (hC k).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (rhsExponent_le_interiorOutputExponent p l target rhsExp))
  obtain ⟨v₂,n₂,D,hu₂,hn₂,he₂,hDnorm,hDerror,hnorm,herror⟩ := interiorResidual_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v₁ S₁
    borrowed (S.R 132) C hC' rfl
    (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster)
    (hready.update_output (raw++S.R 132)) (by simpa [S₁] using h143)
    hcount hrowWidth K hmass
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,hDnorm,hDerror,hnorm,herror⟩
  apply congrArg (mk v₂)
  simp [S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
