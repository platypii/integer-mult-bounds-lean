module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQuarterCount

/-! # Generate normalization from the retained quarter precision header

The quarter-count program preserves every actual precision symbol and generates
the normalization descriptor. The input/interior pipeline then consumes that
owned descriptor before S1 uses its workspace. No normalization header is
supplied in the initial bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def prepareNormalization : Pr P 117 Q A U := quarterCount 100 26 115 116

theorem prepareNormalization_exec (b : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 100).length = 4 * b) (hsaved : S.R 26 = []) (hhalf : S.R 115 = []) (hdst : S.R 116 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body prepareNormalization (mk v S) (22 * b + 10)
        (mk v' { S with R := Function.update S.R 116 (List.replicate b tick) }) := by
  simpa only [prepareNormalization, hdst, List.append_nil] using
    quarterCount_exec (body := body) (count := 100) (saved := 26) (half := 115) (dst := 116) (by decide) b v S hq hsaved hhalf

noncomputable def inputInteriorFromPrecision (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq prepareNormalization (inputInterior hR hQ)

/-- All normalization, multiplier readiness and routing counters are generated
from ordinary headers before the complete input/interior arithmetic executes. -/
theorem inputInteriorFromPrecision_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hquarter : q = 4 * (cExp + e + 1)) (hw : q + (cExp + e + 1) + 4 ≤ w)
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
    ∃ v' m, v'.user = v.user ∧ m ≤ (22 * (cExp + e + 1) + 10) + inputStageCost q cExp e w M L + interiorProductsCost q l w M L ∧
      Exec body (inputInteriorFromPrecision hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
            2 / (2 : ℝ) ^ q := by
  dsimp only
  let source := (List.range M).flatMap C
  let factors := reciprocalWeightWords q ((List.range M).flatMap D)
  let tailX := csyms A w a ++ borrowed
  let S := inputSourceBank q l w M L 0 X Z source factors tail tailX inp out
  obtain ⟨v₁, hu₁, he₁⟩ := prepareNormalization_exec (body := body) (cExp + e + 1) v S
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, hquarter])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank])
  have he₁' : Exec body prepareNormalization (mk v S) (22 * (cExp + e + 1) + 10)
      (mk v₁ (inputSourceBank q l w M L (cExp + e + 1) X Z source factors tail tailX inp out)) := by
    refine he₁.cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (116 : Fin 117)
    · subst k; simp [S, inputSourceBank]
    · simp [S, inputSourceBank, Function.update_apply, hk]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, herr⟩ := inputInterior_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) (cExp := cExp) (e := e) (j := j)
    hR hQ hA hw hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har v₁ tail borrowed inp out
  exact ⟨v₂, (22 * (cExp + e + 1) + 10) + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁' he₂, herr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
