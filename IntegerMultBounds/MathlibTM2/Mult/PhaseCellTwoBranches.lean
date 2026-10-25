module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairScale

/-! # Execute the two Gohberg–Semencul branches in one shared batch

The raw bank contains both generator streams and both input streams explicitly.
Generating this bank (including the repeated right-hand side) is still a setup
obligation; this theorem does not assume a prepared execution or an inverse oracle.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse

/-- Concatenate two equally sized banks of records. -/
def rowBank (M : ℕ) (X Z : ℕ → List GaussianInt) (n : ℕ) : List GaussianInt :=
  if n < M then X n else Z (n - M)

@[simp] theorem rowBank_left (M : ℕ) (X Z : ℕ → List GaussianInt) (n : ℕ) (hn : n < M) :
    rowBank M X Z n = X n := ite_eq_left hn

@[simp] theorem rowBank_right (M : ℕ) (X Z : ℕ → List GaussianInt) (n : ℕ) :
    rowBank M X Z (M + n) = Z n := by
  simp [rowBank, show ¬M + n < M by omega]

/-- The combined raw stream consists of the two original streams in order. -/
theorem rowBank_flatMap (M : ℕ) (X Z : ℕ → List GaussianInt) :
    (List.range (M + M)).flatMap (rowBank M X Z) =
      (List.range M).flatMap X ++ (List.range M).flatMap Z := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro n hn
    exact rowBank_left M X Z n (List.mem_range.mp hn)
  · simp only [rowBank_right]

/-- The compact result retains the branch split; there is no extra permutation. -/
theorem pairRows_rowBank (q l M L : ℕ) (X Z V W : ℕ → List GaussianInt) :
    pairRows q l (M + M) L (rowBank M X Z) (rowBank M V W) =
      pairRows q l M L X V ++ pairRows q l M L Z W := by
  unfold pairRows lowerRows sliceStream
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro n hn
    have hn' := List.mem_range.mp hn
    simp only [upperOperand, rowBank_left M X Z n hn', rowBank_left M V W n hn']
  · simp only [upperOperand, rowBank_right]

theorem rowBank_length {M L : ℕ} (X Z : ℕ → List GaussianInt)
    (hX : ∀ n < M, (X n).length = L) (hZ : ∀ n < M, (Z n).length = L) :
    ∀ n < M + M, (rowBank M X Z n).length = L := by
  intro n hn
  unfold rowBank
  split_ifs with h
  · exact hX n h
  · exact hZ (n - M) (by omega)

theorem rowBank_disk {q M : ℕ} (X Z : ℕ → List GaussianInt)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ n < M + M, ∀ z ∈ rowBank M X Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  intro n hn z hz
  unfold rowBank at hz
  split_ifs at hz with h
  · exact hX n h z hz
  · exact hZ (n - M) (by omega) z hz

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Four triangular products execute with one shared batch charge. All raw
operands and work stacks are restored, and the two compact results prefix the
original output in branch order. -/
theorem twoBranches_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let XB := rowBank M X Z
    let VB := rowBank M V V
    let result := cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w (M + M) L ∧
      Exec body (compactTriangularPair hQ) (mk v (Fixed.startWithTails q l w (M + M) L L XB VB tail tailX [] inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L XB VB result tailX [] inp out)) := by
  dsimp only
  obtain ⟨v', n, hu, hn, he, _⟩ := compactTriangularPair_with_x_tail_exec (body := body) hQ hA hq hw hpad
    (rowBank M X Z) (rowBank M V V) (rowBank_length X Z hlenX hlenZ)
    (rowBank_length V V hlenV hlenV) (rowBank_disk X Z hX hZ) (rowBank_disk V V hV hV)
    v tail tailX inp out
  exact ⟨v', n, hu, hn, by simpa only [pairRows_rowBank] using he⟩


theorem twoBranches_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let XB := rowBank M X Z
    let VB := rowBank M V V
    let result := cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w (M + M) L ∧
      Exec body (compactTriangularPair hQ) (mk v (Fixed.start q l w (M + M) L L XB VB tail inp out)) n
        (mk v' (Fixed.start q l w (M + M) L L XB VB result inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    twoBranches_with_x_tail_exec hQ hA hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
