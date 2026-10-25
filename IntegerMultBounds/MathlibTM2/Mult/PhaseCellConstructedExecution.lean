module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedRun

/-! # Execute the constructed phase-cell arithmetic data

No generator, scalar, similarity-weight range or stage-error oracle is supplied.
The staged bank contains the numerical constructors; generating that setup on
tape, publication and boundary/line composition remain separate obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem constructedCell_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      (cstream A w (executedOutputWords s t p u q l M L j cExp lo C) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧
      m ≤ cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L ∧
      Exec body (cellArithmetic hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap (cellSourceRows L lo C))
          (reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))) tail tailX inp out))
        m (mk v' SF) ∧
      ∀ n : Fin M, (executedRun s t p u q l w M L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hprecision : 13 ≤ 2 ^ 15 * p := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  have htable : ∀ a ∈ executedOutputTable s t p u M L lo,
      0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have hb := weightData_bounds hp hs hαu hθ hgap hbudget (lo (i.val / L)) (L - 1 - i.val % L)
    exact ⟨(by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (8 * p + 1)).trans hb.1, hb.2⟩
  obtain ⟨v', m, huser, hcost, he⟩ := cellArithmetic_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) (cExp := cExp) (e := 8 * p + 1) (j := j)
    hR hQ hA hquarter (by unfold inputExponent at hw; omega) (by unfold inputExponent at hq; omega) hpad
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (cellSourceRows L lo C) (cellWeightRows s t p u L lo)
    (by intro n hn; simp) (by intro n hn; simp) (by intro n hn; simp) (by intro n hn; simp)
    (fun _ _ => columnWords_disk hprecision hs hst hu (by omega) (by omega))
    (fun _ _ => reversedColumnWords_disk hprecision hs hst hu (by omega) (by omega))
    (by
      intro n hn x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact hC n hn _)
    (by intro n hn a ha; exact (cellWeightRows_bounds hp hs hαu hθ hgap hbudget lo n a ha).1)
    (executedOutputTable s t p u M L lo) (by simp [executedOutputTable]) htable
    (reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (reciprocalWord_norm hprecision hs hst hu hL (by omega)) rfl v tail borrowed inp out
  refine ⟨v', m, huser, hcost, ?_, ?_⟩
  · have hV : (fun n => weightedInputNumerators q cExp (8 * p + 1)
        (cellSourceRows L lo C n) (cellWeightRows s t p u L lo n)) = executedInputRows s t p u q L cExp lo C := rfl
    rw [hV] at he
    simpa only [executedOutputWords, executedInteriorWords, inputExponent] using he
  · intro n
    exact executedRun_valid (by omega) hw hp hst hu hαu hθ hgap hbudget hL hq hpad lo C hC n tail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
