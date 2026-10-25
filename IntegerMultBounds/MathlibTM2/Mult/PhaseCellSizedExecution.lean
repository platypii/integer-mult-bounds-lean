module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing

/-! # Published cell execution with the amplified-error precision choice -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem publishedCell_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ borrowed)
    let V := executedInputRows s t p u q L cExp lo C
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    let SF := { S with R := (Function.update (Function.update S.R 111 []) 93
      (cstream A w (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo C)) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧
      m ≤ cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L + publishFromDimensionsCost M L w ∧
      Exec body (publishedCell hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap (cellSourceRows L lo C))
          (reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))) tail tailX inp out))
        m (mk v' SF) ∧
      ∀ n : Fin M, (executedRun s t p u q l w M L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  apply publishedCell_exec hR hQ hA rfl (execution_width_bound p l target rhsExp)
    hp hst hu hαu hθ hgap hbudget hL (execution_stage_bound p l target rhsExp) hpad lo C ?_ v tail borrowed inp out
  intro n hn k
  exact (hC n hn k).trans (pow_le_pow_right₀ (by norm_num) (by unfold sourceExponent; omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
