module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInteriorEncoded
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders

/-! Execute the interior solve and reconstruct the next coupling runtime bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def interiorForCoupling (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (solveHaloInterior hR hQ) installCouplingHeaders

def interiorForCouplingCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  solveHaloInteriorCost p l s t u target rhsExp a b+
    installCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp)
      s t u (PhaseCellBand.width p u) a b

theorem interiorForCoupling_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed outputTail : List (Fin (A+4)))
    (E₀ : ZMod s → GaussianInt)
    (hdst : S.R 132 = cstream A (executionWidth p l target rhsExp) (chirpLine s E₀)++outputTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) S) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ interiorForCouplingCost p l s t u target rhsExp a b ∧
      Exec (embTab groupReg body) (interiorForCoupling hR hQ) (mk v S) n
        (mk v' {S with R := (couplingHeadersR (2^15*p) q s t u band a b
          (Function.update S.R 132 (cstream A w (chirpLine s D)++outputTail)))}) ∧
      CouplingReady (2^15*p) q w s t u band a b (cstream A w (chirpLine s C)++borrowed)
        (embStk groupReg {S with R := (couplingHeadersR (2^15*p) q s t u band a b
          (Function.update S.R 132 (cstream A w (chirpLine s D)++outputTail)))}) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s D)++outputTail)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  obtain ⟨v₁,n₁,D,hu₁,hn₁,hlen,he₁,herror⟩ := solveHaloInterior_encoded_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S
    borrowed outputTail E₀ hdst h127 h138 haMaster hbMaster hready
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++outputTail)}
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u band 0 0 (cstream A w (chirpLine s C)++borrowed) S₁ := by
    apply hready.of_frame (S' := S₁) (S.R 126) (S.R 127) (cstream A w (chirpLine s D)++outputTail) rfl
    funext k
    by_cases h126 : k = 126 <;> by_cases h127' : k = 127 <;> by_cases h132 : k = 132 <;>
      simp [S₁,keyLoopR,h126,h127',h132]
  obtain ⟨v₂,hu₂,he₂,hcoupling⟩ := installCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) (executionStagePrecision p l target rhsExp+1) q l s t u band a b
    (cstream A w (chirpLine s C)++borrowed) v₁ S₁ hready₁
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster)
  have hw : 2*q+8 = w := by dsimp [q,w,executionWidth,executionPrecision]; omega
  have hcoupling' : CouplingReady (2^15*p) q w s t u band a b
      (cstream A w (chirpLine s C)++borrowed)
      (embStk groupReg {S₁ with R := couplingHeadersR (2^15*p) q s t u band a b S₁.R}) := by
    simpa only [hw] using hcoupling
  refine ⟨v₂,n₁+installCouplingHeadersCost (2^15*p) q s t u band a b,D,hu₂.trans hu₁,
    ?_,Exec.seq he₁ he₂,hcoupling',herror⟩
  change n₁+installCouplingHeadersCost (2^15*p) q s t u band a b ≤
    solveHaloInteriorCost p l s t u target rhsExp a b+installCouplingHeadersCost (2^15*p) q s t u band a b
  exact Nat.add_le_add_right hn₁ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
