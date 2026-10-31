module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTwoBranches
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairFinishStock

/-! Actual branch batching retains the compact convolution workspace ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem twoBranches_with_x_tail_exec_within (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hQ) ≤ C) (depth : ℕ) :
    let XB := rowBank M X Z
    let VB := rowBank M V V
    let result := cstream A w (pairRows q l M L X V ++ pairRows q l M L Z V) ++ tail
    ∃ v' n, v'.user = v.user ∧ n ≤ compactPairCost q l w (M + M) L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (Fixed.startWithTails q l w (M+M) L L XB VB tail tailX [] inp out))+depth+
          compactPairWorkspace C q l w (M+M) L) depth (compactTriangularPair hQ) (mk v (Fixed.startWithTails q l w (M + M) L L XB VB tail tailX [] inp out)) n
        (mk v' (Fixed.startWithTails q l w (M + M) L L XB VB result tailX [] inp out)) := by
  dsimp only
  obtain ⟨v', n, hu, hn, he, _⟩ := compactTriangularPair_with_x_tail_exec_within (body := body) hQ hA hq hw hpad
    (rowBank M X Z) (rowBank M V V) (rowBank_length X Z hlenX hlenZ)
    (rowBank_length V V hlenV hlenV) (rowBank_disk X Z hX hZ) (rowBank_disk V V hV hV)
    v tail tailX inp out C hpush depth
  exact ⟨v', n, hu, hn, by simpa only [pairRows_rowBank] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
