module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCellExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime

/-! Closed sized single-cell execution. Numerical setup, ABI transition,
arithmetic, publication and complete cleanup all have executed cost bounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def closedCell (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generatedCell hR hQ) releaseCellRuntime

/-- Complete single-cell time ledger, including every setup and release stage. -/
def sizedClosedCellCost (p l L s t u target rhsExp lo : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let precision := 2 ^ 15 * p
  let band := PhaseCellBand.width p u
  let W := integerSetupWidth precision q (j + 2) 0
  weightedGeneratorSetupCost precision (j + 1) q s t u band L lo +
    prepareCellRuntimeCost precision (j + 1) L q l W + stagePayloadCost 1 L w +
    cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w 1 L +
    publishFromDimensionsCost 1 L w + releaseCellRuntimeCost L q l

theorem closedCell_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L + L ≤ 2 ^ l + 1)
    (lo : ZMod s) (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let source := (List.range 1).flatMap (cellSourceRows L (fun _ => lo) (fun _ => C))
    let rhs := cstream A w source
    ∃ v' m, v'.user = v.user ∧
      m ≤ sizedClosedCellCost p l L s t u target rhsExp lo.val ∧
      Exec body (closedCell hR hQ)
        (mk v (unaryCellBank precision (j + 1) q l s t u band L lo.val rhs borrowed tail inp out)) m
        (mk v' (releasedCellBank rhs borrowed
          (cstream A w (publishedWords 1 L (executedOutputWords s t p u q l 1 L j cExp (fun _ => lo) (fun _ => C))) ++ tail) inp out)) ∧
      ∀ n : Fin 1, (executedRun s t p u q l w 1 L j cExp (fun _ => lo) (fun _ => C) n tail).Valid s t p u lo L
        (fun k => (value q (C k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let precision := 2 ^ 15 * p
  let band := PhaseCellBand.width p u
  let W := integerSetupWidth precision q (j + 2) 0
  let source := (List.range 1).flatMap (cellSourceRows L (fun _ => lo) (fun _ => C))
  let factors := reciprocalWeightWords q ((List.range 1).flatMap (cellWeightRows s t p u L (fun _ => lo)))
  let outs := cstream A w (outputWeightWords q (executedOutputTable s t p u 1 L (fun _ => lo)))
  let rhs := cstream A w source
  let fs := cstream A w factors
  let result := cstream A w (publishedWords 1 L
    (executedOutputWords s t p u q l 1 L j cExp (fun _ => lo) (fun _ => C))) ++ tail
  have hw : w = 2 * q + 8 := by dsimp [q, w, executionWidth, executionPrecision]; omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hvalid⟩ := generatedCell_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC v tail borrowed inp out
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseCellRuntime_exec (body := body)
    precision s t u band L q l W (j + 1) outs fs rhs borrowed tail result inp out v₁
    (by simp [outs, hw, outputWeightWords, executedOutputTable])
    (by simp [fs, factors, hw, reciprocalWeightWords, cellWeightRows])
    (by simp [rhs, source, hw, cellSourceRows])
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hvalid⟩
  dsimp only [sizedClosedCellCost, q, w, j, cExp, precision, band, W] at hm₁ hm₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
