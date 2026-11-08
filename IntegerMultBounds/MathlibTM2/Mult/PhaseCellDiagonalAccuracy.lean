module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedDiagonalPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream

/-! Accuracy of the actual table-D multiplication on published source rows.
The input is already at publication precision; the half-grid inverse target
is retained, as required by the B0 factorization. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.Resampling.WeightTable
variable {s t α p : ℕ} [NeZero s] [NeZero t]

theorem diagonalField_spec (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p) (i : ZMod s) :
    ‖value p (diagonalField s t α p i)-(dPrime s t (α : ℝ) i : ℂ)‖ ≤ 2/(2 : ℝ)^p ∧
      ‖value p (diagonalField s t α p i)‖ ≤ 1 := by
  obtain ⟨herr,hlo,hhi⟩ := tableD_spec s t α p hp hα hαp i
  have hpow : (0 : ℝ) < 2^p := by positivity
  have hv : value p (diagonalField s t α p i) = Complex.ofReal ((tableD s t α p i : ℝ)/(2 : ℝ)^p) := by
    apply Complex.ext <;>
      simp only [value,diagonalField,Complex.ofReal_re,Complex.ofReal_im,Int.cast_zero,zero_div]
  rw [hv,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs]
  constructor
  · have he : (tableD s t α p i : ℝ)/(2 : ℝ)^p-dPrime s t (α : ℝ) i =
        ((tableD s t α p i : ℝ)-(2 : ℝ)^p*dPrime s t (α : ℝ) i)/(2 : ℝ)^p := by
      field_simp
    rw [he,abs_div,abs_of_pos hpow]
    exact div_le_div_of_nonneg_right herr hpow.le
  · rw [abs_of_nonneg (div_nonneg (by exact_mod_cast hlo) hpow.le),div_le_one hpow]
    exact_mod_cast hhi

def diagonalProduct (s t α p : ℕ) (D : ZMod s → GaussianInt) (i : ZMod s) : GaussianInt :=
  tdivN p (D i*diagonalField s t α p i)

theorem diagonalProduct_norm_le (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (D : ZMod s → GaussianInt) (i : ZMod s) :
    ‖value p (diagonalProduct s t α p D i)‖ ≤ ‖value p (D i)‖ := by
  unfold diagonalProduct
  rw [value_tdivN_mul]
  calc
    _ ≤ ‖value p (D i)*value p (diagonalField s t α p i)‖ := norm_rhoC_le p _
    _ = ‖value p (D i)‖*‖value p (diagonalField s t α p i)‖ := norm_mul _ _
    _ ≤ ‖value p (D i)‖*1 := mul_le_mul_of_nonneg_left
      (diagonalField_spec (t := t) hp hα hαp i).2 (norm_nonneg _)
    _ = ‖value p (D i)‖ := mul_one _

theorem diagonalProduct_error (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (D : ZMod s → GaussianInt) (i : ZMod s) (hD : ‖value p (D i)‖ ≤ 2) :
    ‖value p (diagonalProduct s t α p D i)-(dPrime s t (α : ℝ) i : ℂ)*value p (D i)‖ ≤
      6/(2 : ℝ)^p := by
  have hgrid := realScalar_error p (D i) (diagonalField s t α p i)
  have htable := (diagonalField_spec (t := t) hp hα hαp i).1
  have hmul : ‖value p (D i)*value p (diagonalField s t α p i)-
      (dPrime s t (α : ℝ) i : ℂ)*value p (D i)‖ ≤ 4/(2 : ℝ)^p := by
    rw [show value p (D i)*value p (diagonalField s t α p i)-
        (dPrime s t (α : ℝ) i : ℂ)*value p (D i) =
        value p (D i)*(value p (diagonalField s t α p i)-(dPrime s t (α : ℝ) i : ℂ)) by ring,norm_mul]
    calc
      _ ≤ 2*(2/(2 : ℝ)^p) := mul_le_mul hD htable (norm_nonneg _) (by norm_num)
      _ = 4/(2 : ℝ)^p := by ring
  have h := norm_sub_le_norm_sub_add_norm_sub (value p (diagonalProduct s t α p D i))
    (value p (D i)*value p (diagonalField s t α p i)) ((dPrime s t (α : ℝ) i : ℂ)*value p (D i))
  change ‖value p (diagonalProduct s t α p D i)-value p (D i)*value p (diagonalField s t α p i)‖ ≤ _ at hgrid
  exact h.trans ((add_le_add hgrid hmul).trans_eq (by ring))

theorem diagonalProduct_accuracy (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (active : Finset (ZMod s)) (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (error : ℝ)
    (hD : ∀ i ∈ active, ‖value p (D i)‖ ≤ 2)
    (herror : PhaseCellInterface.ErrorOn active (fun i => value p (D i)) z error) :
    PhaseCellInterface.ErrorOn active (fun i => value p (diagonalProduct s t α p D i))
      (fun i => (dPrime s t (α : ℝ) i : ℂ)*z i) (6/(2 : ℝ)^p+error) := by
  intro i hi
  have hd : ‖(dPrime s t (α : ℝ) i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dPrime_nonneg i)]
    exact dPrime_le_one i
  have hm : ‖(dPrime s t (α : ℝ) i : ℂ)*value p (D i)-(dPrime s t (α : ℝ) i : ℂ)*z i‖ ≤ error := by
    rw [←mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans (by simpa using herror i hi)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (diagonalProduct_error hp hα hαp D i (hD i hi)) hm)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
