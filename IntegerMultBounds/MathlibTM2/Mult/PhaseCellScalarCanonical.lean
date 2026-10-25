module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarApply

/-! # Apply the scalar from the canonical post-merge bank and a stored scalar word -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def scalarInput {A : ℕ} (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (xs : List GaussianInt) (a : GaussianInt) (tail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := Fixed.start q l w (M + M) L L X V (cstream A w xs ++ tail) inp out
  { S with R := Function.update S.R 96 (csyms A w a) }

/-- The source generator may retain setup data beneath its counted rows. -/
def scalarInputWithXTail {A : ℕ} (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (xs : List GaussianInt) (a : GaussianInt) (tail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := Fixed.startWithTails q l w (M + M) L L X V (cstream A w xs ++ tail) tailX [] inp out
  { S with R := Function.update S.R 96 (csyms A w a) }

@[simp] theorem scalarInputWithXTail_nil {A : ℕ} (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (xs : List GaussianInt) (a : GaussianInt) (tail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    scalarInputWithXTail q l w M L X V xs a tail [] inp out = scalarInput q l w M L X V xs a tail inp out := by
  simp only [scalarInputWithXTail, Fixed.startWithTails_nil, scalarInput]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- No readiness, binary-counter, scratch-cleanliness or execution oracle is
supplied: the canonical bank determines them. The stored scalar is ordinary
input data; its numerical construction remains the cell setup's obligation. -/
theorem applyCanonical_with_x_tail_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 4 ≤ w)
    (X V : ℕ → List GaussianInt) (xs : List GaussianInt) (a : GaussianInt)
    (hlen : xs.length = M * L) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2)
    (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := scalarInputWithXTail q l w M L X V xs a tail tailX inp out
    let SF := { S with R := (Function.update (counterR q w S.R) 93
      (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w + runCost M L w ∧
      Exec body (applyScalar hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        ‖value q (decodeWord (((SF.R 93).drop (i * w)).take w)) -
          value q (xs[i]) * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  dsimp only
  let S := scalarInputWithXTail q l w M L X V xs a tail tailX inp out
  have hclean : CClean mul S := by
    intro i
    have hi := i.isLt
    constructor
    · rfl
    · have hh := (mul_clean q l w (M + M) L X V (cstream A w xs ++ tail) inp out i).2
      have hn : mul i ≠ (96 : Fin 117) := by
        intro h
        have he := congrArg Fin.val h
        simp only [mul] at he
        omega
      simpa [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, hn,
        show (mul i).val ≠ 110 by simp [mul]; omega, show (mul i).val ≠ 111 by simp [mul]; omega] using hh
  have hfresh (r : CR) : S.R (cr r) = [] := by
    have hr := (cr_range r).2.1
    have hn : cr r ≠ (96 : Fin 117) := by
      intro h
      have he := congrArg Fin.val h
      omega
    simpa [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, hn,
      show (cr r).val ≠ 110 by omega, show (cr r).val ≠ 111 by omega] using
      cr_fresh q l w (M + M) L X V (cstream A w xs ++ tail) inp out r
  exact applyScalar_exec (body := body) hQ hA hq hw xs a hlen hxs ha har v S tail hclean hfresh
    (by simp [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, scalarInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, scalarInputWithXTail])


theorem applyCanonical_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 4 ≤ w)
    (X V : ℕ → List GaussianInt) (xs : List GaussianInt) (a : GaussianInt)
    (hlen : xs.length = M * L) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2)
    (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := scalarInput q l w M L X V xs a tail inp out
    let SF := { S with R := (Function.update (counterR q w S.R) 93
      (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w + runCost M L w ∧
      Exec body (applyScalar hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        ‖value q (decodeWord (((SF.R 93).drop (i * w)).take w)) -
          value q (xs[i]) * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  simpa only [scalarInputWithXTail_nil] using
    applyCanonical_with_x_tail_exec hQ hA hq hw X V xs a hlen hxs ha har v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
