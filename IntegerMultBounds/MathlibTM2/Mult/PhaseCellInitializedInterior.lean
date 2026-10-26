module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInteriorBounded
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput

/-! Initialize the output from the actual RHS and execute a standalone interior pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq initializeInteriorOutput (solveHaloInterior hR hQ)

def initializedInteriorCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  initializeInteriorOutputCost (executionPrecision p l target rhsExp) s+
    solveHaloInteriorCost p l s t u target rhsExp a b

theorem initializedInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
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
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ initializedInteriorCost p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec (embTab groupReg body) (initializedInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132) }) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let raw := cstream A w (chirpLine s C)
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 132 (raw++S.R 132)}
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeInteriorOutput_exec
    (body := embTab groupReg body) q s raw borrowed v S
    (by simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies]))
    (by simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies]))
    hready.source (by simp [raw,hw]) (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  have hC' : ∀ k, ‖value q (C k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro k
    exact (hC k).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (rhsExponent_le_interiorOutputExponent p l target rhsExp))
  obtain ⟨v₂,n₂,D,hu₂,hn₂,hlen,he₂,hnorm,herror⟩ := solveHaloInterior_bounded_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v₁ S₁
    borrowed (S.R 132) C hC' rfl
    (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster)
    (hready.update_output (raw++S.R 132))
  refine ⟨v₂,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hlen,
    (Exec.seq he₁ he₂).cast rfl ?_,hnorm,herror⟩
  apply congrArg (mk v₂)
  simp [S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
