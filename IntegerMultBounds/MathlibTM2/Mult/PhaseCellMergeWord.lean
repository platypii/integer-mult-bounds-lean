module

public import IntegerMultBounds.MathlibTM2.Fast.SubWord
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode

/-! # Exact word subtraction for the phase-cell branch merge -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- One additional guard bit accommodates subtraction without modular aliasing. -/
theorem fits_sub {w : ℕ} (hw : 2 ≤ w) (x y : GaussianInt)
    (hx : Fits (w - 1) x) (hy : Fits (w - 1) y) : Fits w (x - y) := by
  have hp : (2 : ℤ) ^ (w - 1) = 2 * 2 ^ (w - 1 - 1) := by
    calc
      (2 : ℤ) ^ (w - 1) = 2 ^ ((w - 1 - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  constructor
  · change |x.re - y.re| < _
    calc
      _ ≤ |x.re| + |y.re| := abs_sub _ _
      _ < 2 * 2 ^ (w - 1 - 1) := by have := hx.1; have := hy.1; omega
      _ = _ := hp.symm
  · change |x.im - y.im| < _
    calc
      _ ≤ |x.im| + |y.im| := abs_sub _ _
      _ < 2 * 2 ^ (w - 1 - 1) := by have := hx.2; have := hy.2; omega
      _ = _ := hp.symm

theorem value_sub (q : ℕ) (x y : GaussianInt) :
    value q (x - y) = value q x - value q y := by
  apply Complex.ext <;> simp [value, sub_div]

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The actual subtraction automaton consumes the branch words and pushes the
reversed difference. Decoding that output word is exact with one guard bit. -/
theorem mergeWord_exec {a b dst width tmp : Fin T}
    (hreg : [a, b, dst, width, tmp].Nodup) (hA : 96 ≤ A) {w : ℕ} (hw : 2 ≤ w)
    (v : HS T Q A U) (S : Stacks T A) (x y : GaussianInt)
    (rx ry : List (Fin (A + 4)))
    (hx : S.R a = csyms A w x ++ rx) (hy : S.R b = csyms A w y ++ ry)
    (hwidth : (S.R width).length = w) (htmp : S.R tmp = [])
    (hfitsX : Fits (w - 1) x) (hfitsY : Fits (w - 1) y) :
    let SF := { S with R := (Function.update (Function.update (Function.update S.R a rx) b ry) dst
      ((csyms A w (x - y)).reverse ++ S.R dst)) }
    ∃ v', v'.user = v.user ∧
      Exec body (rsbSubWord a b dst width tmp) (mk v S) (5 * w + 6) (mk v' SF) ∧
      decodeWord (((SF.R dst).take w).reverse) = x - y := by
  dsimp only
  obtain ⟨v', hu, he⟩ := subWord_exec (body := body) hreg hA w v S x y rx ry hx hy hwidth htmp
  refine ⟨v', hu, he, ?_⟩
  simp only [Function.update_self]
  rw [List.take_append_of_le_length (by simp [csyms]), List.take_of_length_le (by simp [csyms]),
    List.reverse_reverse]
  exact decodeWord_of_fits (by omega) (by omega) _ (fits_sub hw x y hfitsX hfitsY)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
