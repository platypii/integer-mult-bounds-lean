module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputRows

/-! # Constructed cell execution through coordinate-order publication -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def publishedCell (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (cellArithmetic hR hQ) publishFromDimensions

theorem publishedCell_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L s t p u j cExp : ℕ} [NeZero s] {α d : ℝ}
    (hquarter : q = 4 * inputExponent p cExp) (hw : q + inputExponent p cExp + 2 * l + 6 ≤ w)
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hq : inputExponent p cExp + 2 * l + j + 5 ≤ q)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value q (C n k)‖ ≤ (2 : ℝ) ^ cExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
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
  let precision := 2 ^ 15 * p
  let band := PhaseCellBand.width p u
  let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
  let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
  let a := reciprocalWord precision s t u band L q (j + 2)
  let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ borrowed)
  let V := executedInputRows s t p u q L cExp lo C
  let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
  let words := executedOutputWords s t p u q l M L j cExp lo C
  let SF : Stacks 117 A := { S with R := (Function.update (Function.update S.R 111 []) 93 (cstream A w words ++ tail)) }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hvalid⟩ := constructedCell_exec (body := body)
    hR hQ hA hquarter hw hp hst hu hαu hθ hgap hbudget hL hq hpad lo C hC v tail borrowed inp out
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := publishWords_exec (body := body) M L w words
    (executedOutputWords_length s t p u q l M L j cExp lo C) v₁ SF tail
    (by simp [SF, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]; omega)
    (by simp [SF, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [SF, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [SF])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [SF, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, ?_, hvalid⟩
  refine (Exec.seq he₁ he₂).cast rfl ?_
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = (93 : Fin 117)
  · subst k; simp [SF, words]
  · simp [SF, hk]; rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
