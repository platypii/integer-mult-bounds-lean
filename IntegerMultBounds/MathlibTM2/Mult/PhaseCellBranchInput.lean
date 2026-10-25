module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTwoBranches
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDuplicateStream

/-! # Produce both branch inputs from one raw right-hand-side stream

The combined generator bank and doubled batch header are still explicit setup
inputs. Duplication is executed once, and its cost is included. The repeated
input remains installed in the prepared bank after the branch computation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct

/-- The shared bank initially contains only one copy of the raw input. -/
def singleBranchInput {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := Fixed.start q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail inp out
  { S with R := Function.update S.R 111 (cstream A w ((List.range M).flatMap V)) }

/-- Preserve borrowed generator-side setup data while producing the repeated input. -/
def singleBranchInputWithXTail {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
  { S with R := Function.update S.R 111 (cstream A w ((List.range M).flatMap V)) }

@[simp] theorem singleBranchInputWithXTail_nil {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    singleBranchInputWithXTail q l w M L X Z V tail [] inp out =
      singleBranchInput q l w M L X Z V tail inp out := by
  simp only [singleBranchInputWithXTail, Fixed.startWithTails_nil, singleBranchInput]

/-- The executed duplicate is precisely the combined caller's input format. -/
theorem branch_input_with_x_tail_frame {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := singleBranchInputWithXTail q l w M L X Z V tail tailX inp out
    let rawV := cstream A w ((List.range M).flatMap V)
    { S with R := Function.update S.R 111 (rawV ++ rawV) } =
      Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out := by
  dsimp only
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = (111 : Fin 117)
  · subst k
    simp [singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, rowBank_flatMap, cstream, List.flatMap_append]
  · simp [singleBranchInputWithXTail, hk, Fixed.startWithTails, Fixed.start]

theorem branch_input_frame {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := singleBranchInput q l w M L X Z V tail inp out
    let rawV := cstream A w ((List.range M).flatMap V)
    { S with R := Function.update S.R 111 (rawV ++ rawV) } =
      Fixed.start q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail inp out := by
  simpa only [singleBranchInputWithXTail_nil, Fixed.startWithTails_nil] using
    branch_input_with_x_tail_frame q l w M L X Z V tail [] inp out

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

noncomputable def twoBranchesFromSingleInput (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  .seq (duplicateStream 111 1 2) (compactTriangularPair hQ)

/-- One raw input copy suffices. All four triangular products and the paid
input duplication execute, with both compact branch results in output order. -/
theorem twoBranchesFromSingleInput_with_x_tail_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L ∧
      Exec body (twoBranchesFromSingleInput hQ) (mk v (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail) tailX [] inp out)) := by
  let S := singleBranchInputWithXTail q l w M L X Z V tail tailX inp out
  let rawV := cstream A w ((List.range M).flatMap V)
  have hlen : ((List.range M).flatMap V).length = M * L := by
    calc
      _ = ((List.range M).map (fun _ => L)).sum := by
        rw [List.length_flatMap]
        congr 1
        apply List.map_congr_left
        intro n hn
        exact hlenV n (List.mem_range.mp hn)
      _ = _ := by simp
  have hraw : rawV.length = M * L * w := by simp [rawV, hlen]
  obtain ⟨v₁, hu₁, he₁⟩ := duplicateStream_exec (body := body)
    (src := 111) (buf := 1) (tmp := 2) (by decide) v S rawV
    (by simp [S, singleBranchInputWithXTail, rawV])
    (by simp [S, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  have he₁' := he₁.cast (by rw [hraw])
    (congrArg (mk v₁) (branch_input_with_x_tail_frame q l w M L X Z V tail tailX inp out))
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := twoBranches_with_x_tail_exec (body := body)
    hQ hA hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV v₁ tail tailX inp out
  exact ⟨v₂, (6 * (M * L * w) + 6) + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁' he₂⟩


theorem twoBranchesFromSingleInput_exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L ∧
      Exec body (twoBranchesFromSingleInput hQ) (mk v (singleBranchInput q l w M L X Z V tail inp out)) n
        (mk v' (Fixed.start q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
          (cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail) inp out)) := by
  simpa only [singleBranchInputWithXTail_nil, Fixed.startWithTails_nil] using
    twoBranchesFromSingleInput_with_x_tail_exec hQ hA hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV
      v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
