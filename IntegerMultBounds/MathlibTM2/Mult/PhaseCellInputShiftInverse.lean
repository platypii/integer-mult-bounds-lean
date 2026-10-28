module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputPrecision
public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec

/-! The input conversion is reversible without retaining a second copy of the source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem inputShift_tdiv (d : ℕ) (z : GaussianInt) :
    tdivN d ((2 : GaussianInt)^d*z) = z := by
  have hp : (⟨(2 : ℤ)^d,0⟩ : GaussianInt) = (2 : GaussianInt)^d := by
    induction d with
    | zero => rfl
    | succ d ih =>
      conv_rhs => rw [pow_succ,←ih]
      change (⟨(2 : ℤ)^(d+1),0⟩ : GaussianInt) = ⟨(2 : ℤ)^d,0⟩*⟨2,0⟩
      ext <;> simp [mul_real_re,mul_real_im,pow_succ]
  rw [mul_comm,←hp]
  ext
  · rw [tdivN_re,mul_real_re,Int.mul_tdiv_cancel _ (by positivity)]
  · rw [tdivN_im,mul_real_im,Int.mul_tdiv_cancel _ (by positivity)]

theorem inputShift_roundtrip (d : ℕ) (xs : List GaussianInt) :
    (xs.map (fun z => (2 : GaussianInt)^d*z)).map (tdivN d) = xs := by
  simp only [List.map_map,Function.comp_def,inputShift_tdiv]
  change xs.map id = xs
  exact List.map_id xs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
