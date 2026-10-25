module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResultPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLowerCrop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTriangularPairRestore

/-! # Compact and publish the triangular pair, releasing both padded results -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def pairRows (q l M L : ℕ) (X V : ℕ → List GaussianInt) : List GaussianInt :=
  lowerRows q l M L X (upperOperand q l L X V)

def pairFinishCost (l w M L : ℕ) : ℕ :=
  (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) + 4 * w + 6 * 2 ^ l * w + 9 * l + 22) +
  (2 * (12 * (M * (2 ^ l * w)) + 9 * M + 4 * w + 6 * (2 ^ l * w) + 9 * l + 26) +
    4 * (M * L * w) + 4)

/-- Port 12 holds only the cropped result, and is cleared before returning. -/
def finishTriangularPair : Pr P 117 Q A U :=
  .seq (upperCropFromDimensions 101 108 1 2 3 103 4 94 5 93 6 7 8 9 10 11 12)
    (publishPairResult 101 94 2 5 108 4 93 9 10 11 12 6)

/-- Exact canonical-bank endpoint: every temporary stream and work port is released. -/
theorem finishTriangularPair_with_x_tail_exec {q l w M L : ℕ}
    (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let xs := cstream A w (Fixed.result q l M X (upperOperand q l L X V))
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse))
    ∃ v' n, v'.user = v.user ∧ n ≤ pairFinishCost l w M L ∧
      Exec body finishTriangularPair (mk v (Fixed.startWithTails q l w M L L X V (xs ++ (ys ++ tail)) tailX [] inp out)) n
        (mk v' (Fixed.startWithTails q l w M L L X V (cstream A w (pairRows q l M L X V) ++ tail) tailX [] inp out)) := by
  dsimp only
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  let W := upperOperand q l L X V
  let xs := cstream A w (Fixed.result q l M X W)
  let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse))
  let zs := cstream A w (pairRows q l M L X V)
  let S := Fixed.startWithTails q l w M L L X V (xs ++ (ys ++ tail)) tailX [] inp out
  have hlenW : ∀ j < M, (W j).length = L := fun j _ => upperOperand_length hL X V j
  have hW := upperOperand_disk hpad X V hlenX hlenV hX hV
  have hx : xs.length = M * (2 ^ l * w) := by simp [xs, Fixed.result, Nat.mul_assoc]
  have hy : ys.length = M * (2 ^ l * w) := by simp [ys, Fixed.result, Nat.mul_assoc]
  have hz : zs.length = M * L * w := by
    have hh := sliceStream_length M 0 L (show 0 + L ≤ 2 ^ l by omega) (fun j => coeff q l (X j) (W j))
    simpa [zs, pairRows, lowerRows, W] using congrArg (fun n => n * w) hh
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := lowerCropFromDimensions_exec (body := body)
    (lR := 101) (dst := 12) (batch := 108) (batchSaved := 1) (skip := 2) (savedSkip := 3)
    (mR := 103) (recordSaved := 4) (wordR := 94) (recordSymbols := 5) (src := 93)
    (acc := 6) (current := 7) (savedSource := 8) (saved := 9) (buf := 10) (tmp := 11)
    (by decide) hA hw hpad X W hlenX hlenW hX hW v S (ys ++ tail)
    (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]) (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, xs, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]) (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 12 zs }
  have he₁' : Exec body (upperCropFromDimensions 101 108 1 2 3 103 4 94 5 93 6 7 8 9 10 11 12)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, S₁, zs, pairRows, W] using he₁
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := publishPairResult_exec (body := body)
    (lR := 101) (width := 94) (skip := 2) (ringSymbols := 5) (batch := 108) (count := 4)
    (src := 93) (saved := 9) (buf := 10) (tmp := 11) (compact := 12) (acc := 6)
    (by decide) l w M v₁ S₁ xs ys zs tail
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]) (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]) hx hy (by simp [S₁])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, ?_, (Exec.seq he₁' he₂).cast rfl ?_⟩
  · rw [hz] at hn₂
    unfold pairFinishCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (12 : Fin 117)
    · subst k
      simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    · by_cases ho : k.val = 93
      · have heq : k = (93 : Fin 117) := Fin.ext ho
        subst k
        simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, zs]
      · have h93 : k ≠ (93 : Fin 117) := fun h => ho (congrArg Fin.val h)
        simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, hk, ho, h93]

theorem finishTriangularPair_exec {q l w M L : ℕ}
    (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let xs := cstream A w (Fixed.result q l M X (upperOperand q l L X V))
    let ys := cstream A w (Fixed.result q l M X (fun n => (V n).reverse))
    ∃ v' n, v'.user = v.user ∧ n ≤ pairFinishCost l w M L ∧
      Exec body finishTriangularPair (mk v (Fixed.start q l w M L L X V (xs ++ (ys ++ tail)) inp out)) n
        (mk v' (Fixed.start q l w M L L X V (cstream A w (pairRows q l M L X V) ++ tail) inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    finishTriangularPair_with_x_tail_exec hA hw hpad X V hlenX hlenV hX hV
      v tail [] inp out

/-- Full reusable triangular pair: ordinary inputs in, one compact output prefix out. -/
noncomputable def compactTriangularPair (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  .seq (triangularPairRestored hQ) finishTriangularPair

def compactPairCost (q l w M L : ℕ) : ℕ :=
  2 * Fixed.cost q l w M +
    2 * (M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20) +
    (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
      4 * w + 6 * 2 ^ l * w + 9 * l + 22) +
    (12 * (M * L * w) + 9 * M + 6 * (L * w) + 9 * L + 18) + pairFinishCost l w M L

/-- Setup, both products, compaction and release execute on the same 117 tapes.
Only the compact result is prefixed to the original output; the numerical lower
stage is interpreted against the actual normalized upper numerators. -/
theorem compactTriangularPair_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let SF := Fixed.startWithTails q l w M L L X V (cstream A w (pairRows q l M L X V) ++ tail) tailX [] inp out
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w M L ∧
      Exec body (compactTriangularPair hQ) (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)) n (mk v' SF) ∧
      ∀ j < M, ∀ i : Fin L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * L + (L - 1 - i.val)) * w)).take w)) -
          lower (fun k => value q (block (X j) k))
            (fun k => value q (block (upperOperand q l L X V j) k)) i.val‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁, _⟩ := triangularPairRestored_with_x_tail_exec (body := body)
    hQ hA hq hw hpad X V hlenX hlenV hX hV v tail tailX inp out
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := finishTriangularPair_with_x_tail_exec (body := body)
    hA hw hpad X V hlenX hlenV hX hV v₁ tail tailX inp out
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by unfold compactPairCost; omega, Exec.seq he₁ he₂, ?_⟩
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  intro j hj i
  simpa [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, Fixed.ringReg, pairRows] using
    lowerRows_error hA hw hpad X (upperOperand q l L X V) hlenX
      (fun n _ => upperOperand_length hL X V n) hX
      (upperOperand_disk hpad X V hlenX hlenV hX hV) tail j hj i


theorem compactTriangularPair_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let SF := Fixed.start q l w M L L X V (cstream A w (pairRows q l M L X V) ++ tail) inp out
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w M L ∧
      Exec body (compactTriangularPair hQ) (mk v (Fixed.start q l w M L L X V tail inp out)) n (mk v' SF) ∧
      ∀ j < M, ∀ i : Fin L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
          (((SF.R (Fixed.ringReg .out)).drop ((j * L + (L - 1 - i.val)) * w)).take w)) -
          lower (fun k => value q (block (X j) k))
            (fun k => value q (block (upperOperand q l L X V j) k)) i.val‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  simpa only [Fixed.startWithTails_nil] using
    compactTriangularPair_with_x_tail_exec hQ hA hq hw hpad X V hlenX hlenV hX hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
