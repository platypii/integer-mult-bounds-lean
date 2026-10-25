module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedExecution

/-! Execute the sized single-cell inverse directly from constructed numerical
setup, including the ABI transition and publication of its valid result. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructionCell (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq prepareCellRuntime (stagedCell hR hQ)

theorem constructionCell_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hpad : L + L ≤ 2 ^ l + 1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < 1, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let W := integerSetupWidth precision q (j + 2) 0
    let source := (List.range 1).flatMap (cellSourceRows L lo C)
    let factors := reciprocalWeightWords q ((List.range 1).flatMap (cellWeightRows s t p u L lo))
    let outs := cstream A w (outputWeightWords q (executedOutputTable s t p u 1 L lo))
    let rhs := cstream A w source
    let fs := cstream A w factors
    let S := cellConstructionBank precision (j + 1) q l L W outs fs rhs borrowed tail inp out
    let B := cellRuntimeBank precision s t u band L q l W (j + 1) outs fs rhs borrowed tail inp out
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCellRuntimeCost precision (j + 1) L q l W + stagePayloadCost 1 L w +
        cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w 1 L + publishFromDimensionsCost 1 L w ∧
      Exec body (constructionCell hR hQ)
        (mk v (packedGeneratorBank (constructedFactorBank S precision s t u band L W)
          precision s t u band L q W (j + 2))) m
        (mk v' { B with R := (Function.update B.R 93
          (cstream A w (publishedWords 1 L (executedOutputWords s t p u q l 1 L j cExp lo C)) ++ tail)) }) ∧
      ∀ n : Fin 1, (executedRun s t p u q l w 1 L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let precision := 2 ^ 15 * p
  let band := PhaseCellBand.width p u
  let W := integerSetupWidth precision q (j + 2) 0
  let source := (List.range 1).flatMap (cellSourceRows L lo C)
  let factors := reciprocalWeightWords q ((List.range 1).flatMap (cellWeightRows s t p u L lo))
  let outs := cstream A w (outputWeightWords q (executedOutputTable s t p u 1 L lo))
  let rhs := cstream A w source
  let fs := cstream A w factors
  have hw : w = 2 * q + 8 := by
    dsimp [q, w, executionWidth, executionPrecision]
    omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepareCanonicalCellRuntime_exec (body := body)
    precision s t u band L q l W (j + 1) outs fs rhs borrowed tail inp out v
    (by simp [outs, hw, outputWeightWords, executedOutputTable])
    (by simp [fs, factors, hw, reciprocalWeightWords, List.length_flatMap, cellWeightRows])
    (by simp [rhs, source, hw, cellSourceRows])
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hvalid⟩ := stagedCell_sized_exec (body := body)
    (M := 1) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC v₁ tail borrowed inp out
  have he₂' : Exec body (stagedCell hR hQ)
      (mk v₁ (cellRuntimeBank precision s t u band L q l W (j + 1) outs fs rhs borrowed tail inp out)) m₂
      (mk v₂ { cellRuntimeBank precision s t u band L q l W (j + 1) outs fs rhs borrowed tail inp out with
        R := (Function.update (cellRuntimeBank precision s t u band L q l W (j + 1) outs fs rhs borrowed tail inp out).R 93
          (cstream A w (publishedWords 1 L (executedOutputWords s t p u q l 1 L j cExp lo C)) ++ tail)) }) := by
    simpa only [cellRuntimeBank_eq_inputSourceBank, ← hw] using he₂
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂', hvalid⟩
  dsimp only [q, w, j, cExp, precision, band, W] at hm₁ hm₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
