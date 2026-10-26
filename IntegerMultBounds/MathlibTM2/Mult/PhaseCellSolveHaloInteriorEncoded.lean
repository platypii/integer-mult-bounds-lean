module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedAmbient

/-! The actual interior solve returns an encoded ambient integer field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem solveHaloInterior_encoded_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ solveHaloInteriorCost p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec (embTab groupReg body) (solveHaloInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++outputTail) }) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s D)++outputTail)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let w := executionWidth p l target rhsExp
  obtain ⟨v',n,E',hu,hn,hE',he,herror,hencoded⟩ := solveHaloInterior_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad C hC x hx v S
    borrowed (cstream A w (chirpLine s E₀)) outputTail (by simp [w]) hdst
    h127 h138 haMaster hbMaster hready
  obtain ⟨D,hD⟩ := encodedStream_ambient (s := s) (by dsimp [w,executionWidth]; omega) E' hE'
    (hencoded ⟨chirpLine s E₀,rfl⟩)
  refine ⟨v',n,D,hu,hn,by simp,?_,?_⟩
  · simpa only [hD] using he
  · simpa only [hD] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
