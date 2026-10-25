module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorFrame

/-! # A concrete finite register allocation for the complete output arithmetic

64 multiplier tapes, two thirty-role data banks sharing one intermediate, and
22 control/scratch tapes fit in 146 tapes. The allocation is independent of all
input dimensions and coefficient values.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement

open IntegerMultBounds.MathlibTM2.Fast

def code : CR → Fin 30
  | .xs => 0 | .ys => 1 | .xsv => 2 | .ysv => 3 | .acc => 4 | .out => 5
  | .wn => 6 | .pn => 7 | .nn => 8 | .tmp => 9
  | .u0 => 10 | .u1 => 11 | .u2 => 12 | .u3 => 13
  | .ma => 14 | .mb => 15 | .mc => 16 | .md => 17
  | .sa => 18 | .sb => 19 | .sc => 20 | .sd => 21
  | .p1 => 22 | .p2 => 23 | .p3 => 24 | .p4 => 25
  | .qr => 26 | .qi => 27 | .sr => 28 | .si => 29

theorem code_injective : Function.Injective code := by
  intro r s h
  cases r <;> cases s <;> simp_all [code]

def cr (r : CR) : Fin 146 := ⟨64 + (code r).val, by have := (code r).isLt; omega⟩
def nr (r : CR) : Fin 146 := if r = .xs then cr .out else ⟨94 + (code r).val, by have := (code r).isLt; omega⟩
def mul (i : Fin 64) : Fin 146 := ⟨i.val, by omega⟩
def bank (i : Fin 22) : Fin 146 := ⟨124 + i.val, by omega⟩

theorem cr_injective : Function.Injective cr := by
  intro r s h
  apply code_injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cr] at hv
  omega

theorem nr_injective : Function.Injective nr := by
  intro r s h
  have hv := congrArg Fin.val h
  by_cases hr : r = .xs
  · subst r
    by_cases hs : s = .xs
    · exact hs.symm
    · simp only [nr, ite_true, ite_eq_right hs, cr, code] at hv
      have := (code s).isLt
      omega
  · by_cases hs : s = .xs
    · subst s
      simp only [nr, ite_true, ite_eq_right hr, cr, code] at hv
      have := (code r).isLt
      omega
    · simp only [nr, ite_eq_right hr, ite_eq_right hs] at hv
      apply code_injective
      apply Fin.ext
      omega

theorem nr_cr (r s : CR) (hr : r ≠ .xs) : nr r ≠ cr s := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nr, ite_eq_right hr, cr] at hv
  have := (code s).isLt
  omega

def layout : ChirpOutputLayout 146 where
  cr := cr
  nr := nr
  mul := mul
  bank := bank
  cr_inj := cr_injective
  nr_inj := nr_injective
  mul_inj := by
    intro i j h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  bank_inj := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [bank] at hv
    omega
  cr_mul := by
    intro r i h
    have hv := congrArg Fin.val h
    simp only [cr, mul] at hv
    omega
  nr_mul := by
    intro r i h
    have hv := congrArg Fin.val h
    by_cases hr : r = .xs
    · subst r; simp only [nr, ite_true, cr, code, mul] at hv; omega
    · simp only [nr, ite_eq_right hr, mul] at hv; omega
  bank_cr := by
    intro i r h
    have hv := congrArg Fin.val h
    simp only [bank, cr] at hv
    have := (code r).isLt
    omega
  bank_nr := by
    intro i r h
    have hv := congrArg Fin.val h
    by_cases hr : r = .xs
    · subst r; simp only [nr, ite_true, cr, code, bank] at hv; omega
    · simp only [nr, ite_eq_right hr, bank] at hv; have := (code r).isLt; omega
  bank_mul := by
    intro i j h
    have hv := congrArg Fin.val h
    simp only [bank, mul] at hv
    omega
  link := by simp only [nr, ite_true]
  input_frame := by
    intro r h
    have hv := congrArg Fin.val h
    by_cases hr : r = .xs
    · subst r; simp only [nr, ite_true, cr, code] at hv; norm_num at hv
    · simp only [nr, ite_eq_right hr, cr, code] at hv; omega

theorem layout_cross : layout.Cross := nr_cr

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement
