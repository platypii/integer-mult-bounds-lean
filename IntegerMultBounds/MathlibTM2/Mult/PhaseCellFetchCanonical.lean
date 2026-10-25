module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarFetch
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixed

/-! # Retained scalar access on the canonical tailed generator bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem rawRows_length (w B L : ℕ) (X : ℕ → List GaussianInt)
    (hlen : ∀ n < B, (X n).length = L) :
    (cstream A w ((List.range B).flatMap X)).length = B * L * w := by
  have hh := length_flatten_const ((List.range B).map X) (by
    intro xs hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact hlen n (List.mem_range.mp hn))
  have hflat : ((List.range B).flatMap X).length = B * L := by
    simpa only [List.flatMap_def, List.length_map, List.length_range] using hh
  simp [hflat]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- The scalar word survives under the generator bank, is fetched at its counted
position, and remains in its original storage after the copy. -/
theorem fetchCanonical_exec (q l w B L : ℕ) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < B, (X n).length = L) (a : GaussianInt)
    (v : HS 117 Q A U) (outTail borrowed : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w B L L X V outTail (csyms A w a ++ borrowed) [] inp out
    ∃ v' m, v'.user = v.user ∧ m ≤ fetchScalarCost B L w ∧
      Exec body fetchScalar (mk v S) m (mk v' { S with R := Function.update S.R 96 (csyms A w a) }) := by
  dsimp only
  let S := Fixed.startWithTails q l w B L L X V outTail (csyms A w a ++ borrowed) [] inp out
  apply fetchScalar_exec (body := body) B L w (cstream A w ((List.range B).flatMap X)) borrowed a v S
  · simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  · simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  · simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  · exact rawRows_length w B L X hlenX
  · simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
