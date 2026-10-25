module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorProducts

/-! # Execute normalized input production followed by the interior arithmetic

The input-weight output is installed in the exact S1 bank before the four
triangular products, merge and retained reciprocal multiplication run. Borrowed
generator-side setup survives both stages. Setup-data generation and final
output-stage bank preparation remain separate obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def inputInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (inputStage hQ) (interiorProducts hR hQ)

/-- All normalized inputs are produced from raw RHS words on tape. The endpoint
is the actual scalar interior stream, with only its explicit repeated-input
bank and three readiness counters retained. -/
theorem inputInterior_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hw : q + (cExp + e + 1) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z C : ℕ → List GaussianInt) (D : ℕ → List ℚ)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenC : ∀ n < M, (C n).length = L) (hlenD : ∀ n < M, (D n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hC : ∀ n < M, ∀ z ∈ C n, ‖value q z‖ ≤ (2 : ℝ) ^ cExp)
    (hD : ∀ n < M, ∀ a ∈ D n, 1 / (2 : ℝ) ^ e ≤ (a : ℝ))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
    let tailX := csyms A w a ++ borrowed
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    let SF := { S with R := (Function.update (ScalarPlacement.counterR q w S.R) 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ inputStageCost q cExp e w M L + interiorProductsCost q l w M L ∧
      Exec body (inputInterior hR hQ)
        (mk v (inputSourceBank q l w M L (cExp + e + 1) X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
            2 / (2 : ℝ) ^ q := by
  dsimp only
  let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := inputStage_exec (body := body) hQ hA hw hq X Z C D
    hlenC hlenD hC hD v tail (csyms A w a ++ borrowed) inp out
  have hlenV : ∀ n < M, (V n).length = L := by
    intro n hn
    simpa only [V, weightedInputNumerators_length q cExp e (C n) (D n)
      ((hlenC n hn).trans (hlenD n hn).symm)] using hlenC n hn
  have hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) :=
    fun n hn => weightedInputNumerators_disk (C n) (D n) (hC n hn) (hD n hn)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, herr⟩ := interiorProducts_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L)
    hR hQ hA (by omega) (by omega) hpad X Z V hlenX hlenZ hlenV hX hZ hV a ha har v₁ tail borrowed inp out
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, herr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
