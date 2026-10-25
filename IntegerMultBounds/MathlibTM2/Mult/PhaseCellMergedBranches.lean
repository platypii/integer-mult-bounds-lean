module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedMerge

/-! # The four triangular products followed by their executed branch difference -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem pairRows_length {l L : ℕ} (hL : L ≤ 2 ^ l) (q M : ℕ) (X V : ℕ → List GaussianInt) :
    (pairRows q l M L X V).length = M * L := by
  exact sliceStream_length M 0 L (by omega) _

/-- A coordinate of the actual compact branch stream, in its stored reversed-row order. -/
def pairNumerator (q l M L : ℕ) (X V : ℕ → List GaussianInt)
    (i : Fin (M * L)) : GaussianInt :=
  block (pairRows q l M L X V) i.val

theorem pairNumerator_stream (q l M L : ℕ) (hL : L ≤ 2 ^ l) (X V : ℕ → List GaussianInt) :
    List.ofFn (pairNumerator q l M L X V) = pairRows q l M L X V := by
  apply List.ext_getElem
  · simp [pairRows_length hL]
  · intro i hi hj
    simp [pairNumerator, block, hj]

/-- Stored numerators for the difference of the two computed branches. -/
def branchDifference (q l M L : ℕ) (X Z V : ℕ → List GaussianInt) : List GaussianInt :=
  List.ofFn (fun i => pairNumerator q l M L X V i - pairNumerator q l M L Z V i)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

noncomputable def mergedBranches (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  .seq (twoBranchesFromSingleInput hQ) fixedBranchMerge

/-- The repeated-input producer, all four products, routing-count generation,
subtraction and publication execute on 117 tapes. Only the merged compact output
is retained, together with the explicitly prepared repeated-input bank. -/
theorem mergedBranches_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L + fixedMergeCost w M L ∧
      Exec body (mergedBranches hQ) (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (branchDifference q l M L X Z V) ++ tail) tailX [] inp out)) := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hL : L ≤ 2 ^ l := by omega
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := twoBranchesFromSingleInput_with_x_tail_exec (body := body)
    hQ (by omega) hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV v tail tailX inp out
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := fixedBranchMerge_with_x_tail_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) hA (by omega)
    (rowBank M X Z) (rowBank M V V) (pairNumerator q l M L X V)
    (pairNumerator q l M L Z V) v₁ tail tailX inp out
  simp only [pairNumerator_stream q l M L hL] at he₂
  rw [cstream_append, List.append_assoc] at he₁
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩


theorem mergedBranches_exec (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L + fixedMergeCost w M L ∧
      Exec body (mergedBranches hQ) (mk v (singleBranchInput q l w M L X Z V tail inp out)) n
        (mk v' (Fixed.start q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (branchDifference q l M L X Z V) ++ tail) inp out)) := by
  simpa only [singleBranchInputWithXTail_nil, Fixed.startWithTails_nil] using
    mergedBranches_with_x_tail_exec hQ hA hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
