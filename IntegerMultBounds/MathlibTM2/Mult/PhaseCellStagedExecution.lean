module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPayloadBank

/-! # Sized cell execution from empty work buffers and preserved payload

The reusable setup and per-call payload are preserved exactly. Owned RHS and
reciprocal copies are generated before arithmetic and released by the caller.
Gathering/packing the payload and generating setup remain separate costs.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def stagedCell (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq stagePayload (publishedCell hR hQ)

theorem stagedCell_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l M L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
    let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
    let a := reciprocalWord precision s t u band L q (j + 2)
    let source := (List.range M).flatMap (cellSourceRows L lo C)
    let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
    let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ payload)
    let S := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo C)) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧
      m ≤ stagePayloadCost M L w + cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L + publishFromDimensionsCost M L w ∧
      Exec body (stagedCell hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out))
        m (mk v' SF) ∧
      ∀ n : Fin M, (executedRun s t p u q l w M L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let source := (List.range M).flatMap (cellSourceRows L lo C)
  let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
  let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := stagePayloadBank_exec (body := body) q l w M L
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (by intro n hn; simp) (by intro n hn; simp)
    (reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (outputWeightWords q (executedOutputTable s t p u M L lo)) source factors
    (by simp [outputWeightWords, executedOutputTable])
    (by simp [source, List.length_flatMap, cellSourceRows])
    (by simp [factors, reciprocalWeightWords, List.length_flatMap, cellWeightRows])
    v tail borrowed inp out
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hvalid⟩ := publishedCell_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC v₁ tail payload inp out
  dsimp only [w] at hm₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, ?_, hvalid⟩
  refine (Exec.seq he₁ he₂).cast rfl ?_
  congr 1
  apply emptyInputBank_output_frame

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
