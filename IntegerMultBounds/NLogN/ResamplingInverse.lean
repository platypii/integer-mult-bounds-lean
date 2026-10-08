import IntegerMultBounds.NLogN.Resampling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Section 4.2 of Harvey and van der Hoeven: solving the resampling system.
The row-selecting map `C`, the square subsystem `T' = C T`, the diagonal map
`D`, and the normalisation `N = T' D = 1 + E` are defined as in the paper.
Proved: the explicit formula for `T'`, the decomposition `N = 1 + E`, the
termwise exponent inequality, and Lemma 4.6: `‖E u‖ ≤ 2.01 e^{-π α² θ / 2}`
entrywise for `‖u‖ ≤ 1` when `α² θ ≥ 1`, hence `‖E u‖ ≤ 1/2`. The
left inverse `D N⁻¹ C` of `T` is assembled elsewhere from these facts; no
fixed-point approximation is part of this file. -/

namespace IntegerMultBounds.NLogN

open Real

/-! ### Nearest integer and fractional part -/

/-- `[x] = ⌊x + 1/2⌋`, the nearest integer, rounding up on ties. -/
noncomputable def nearest (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- `⟨x⟩ = x - [x] ∈ [-1/2, 1/2)`. -/
noncomputable def frac (x : ℝ) : ℝ := x - nearest x

theorem frac_bounds (x : ℝ) : -1 / 2 ≤ frac x ∧ frac x < 1 / 2 := by
  unfold frac nearest
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

theorem abs_frac_le (x : ℝ) : |frac x| ≤ 1 / 2 := by
  have := frac_bounds x
  rw [abs_le]
  constructor <;> linarith

theorem sq_frac_le (x : ℝ) : frac x ^ 2 ≤ 1 / 4 := by
  have h := abs_frac_le x
  have h2 : |frac x| ^ 2 ≤ (1 / 2) ^ 2 := by
    gcongr
  rw [sq_abs] at h2
  linarith

theorem nearest_add_int (x : ℝ) (n : ℤ) : nearest (x + n) = nearest x + n := by
  unfold nearest
  rw [show x + n + 1 / 2 = (x + 1 / 2) + n by ring, Int.floor_add_intCast]

theorem frac_add_int (x : ℝ) (n : ℤ) : frac (x + n) = frac x := by
  unfold frac
  rw [nearest_add_int]
  push_cast
  ring

theorem nearest_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ nearest x := by
  unfold nearest
  exact Int.floor_nonneg.mpr (by linarith)

section Setup

variable (s t : ℕ) [NeZero s] [NeZero t]

/-! ### The offsets `β_ℓ` -/

/-- `β_ℓ = ⟨tℓ/s⟩`. -/
noncomputable def beta (ℓ : ℤ) : ℝ := frac ((t : ℝ) * ℓ / s)

omit [NeZero s] [NeZero t] in
theorem abs_beta_le (ℓ : ℤ) : |beta s t ℓ| ≤ 1 / 2 := abs_frac_le _

omit [NeZero s] [NeZero t] in
theorem sq_beta_le (ℓ : ℤ) : beta s t ℓ ^ 2 ≤ 1 / 4 := sq_frac_le _

omit [NeZero t] in
theorem beta_add_mul (ℓ q : ℤ) : beta s t (ℓ + s * q) = beta s t ℓ := by
  unfold beta
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  rw [show (t : ℝ) * ((ℓ + s * q : ℤ) : ℝ) / s = (t : ℝ) * ℓ / s + ((t * q : ℤ) : ℝ) by
    push_cast
    field_simp]
  exact frac_add_int _ _

omit [NeZero t] in
theorem beta_periodic (ℓ : ℤ) : beta s t (ℓ + s) = beta s t ℓ := by
  simpa using beta_add_mul s t ℓ 1

omit [NeZero t] in
theorem beta_intCast_val (a : ℤ) : beta s t ((a : ZMod s).val : ℤ) = beta s t a := by
  rw [ZMod.val_intCast, Int.emod_def, show a - s * (a / s) = a + s * (-(a / s)) by ring]
  exact beta_add_mul s t a _

omit [NeZero t] in
theorem beta_val_add (ℓ : ZMod s) (h : ℤ) :
    beta s t ((ℓ + (h : ZMod s)).val : ℤ) = beta s t (ℓ.val + h) := by
  have : ℓ + (h : ZMod s) = ((ℓ.val + h : ℤ) : ZMod s) := by
    push_cast
    simp
  rw [this, beta_intCast_val]

/-! ### The row-selecting map `C` -/

/-- `[tℓ/s]` as a natural number. -/
noncomputable def rowIndexNat (ℓ : ZMod s) : ℕ := (nearest ((t : ℝ) * ℓ.val / s)).toNat

omit [NeZero s] [NeZero t] in
theorem rowIndexNat_cast (ℓ : ZMod s) :
    ((rowIndexNat s t ℓ : ℕ) : ℝ) = ((nearest ((t : ℝ) * ℓ.val / s) : ℤ) : ℝ) := by
  unfold rowIndexNat
  have h0 : 0 ≤ nearest ((t : ℝ) * ℓ.val / s) := nearest_nonneg (by positivity)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

omit [NeZero t] in
theorem rowIndexNat_lt (hst : s < t) (ℓ : ZMod s) : rowIndexNat s t ℓ < t := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hv : (ℓ.val : ℝ) + 1 ≤ s := by exact_mod_cast ℓ.val_lt
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  have hx : (t : ℝ) * ℓ.val / s + 1 / 2 < t := by
    rw [div_add' _ _ _ hs.ne', div_lt_iff₀ hs]
    nlinarith
  have hn : nearest ((t : ℝ) * ℓ.val / s) < (t : ℤ) := by
    unfold nearest
    exact Int.floor_lt.mpr (by exact_mod_cast hx)
  unfold rowIndexNat
  omega

/-- The map `ℓ ↦ [tℓ/s]` from `ZMod s` to `ZMod t`. -/
noncomputable def rowIndex (ℓ : ZMod s) : ZMod t := (rowIndexNat s t ℓ : ZMod t)

omit [NeZero t] in
theorem rowIndex_val (hst : s < t) (ℓ : ZMod s) :
    (rowIndex s t ℓ).val = rowIndexNat s t ℓ :=
  ZMod.val_natCast_of_lt (rowIndexNat_lt s t hst ℓ)

/-- The paper's `C`: `(C u)_ℓ = u_{[tℓ/s]}`. -/
noncomputable def rowSelect (u : ZMod t → ℂ) : ZMod s → ℂ := fun ℓ => u (rowIndex s t ℓ)

/-! ### The square subsystem `T' = C T` -/

/-- `T' = C T`. -/
noncomputable def squareT (α : ℝ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  rowSelect s t (resampT s t α u)

/-- `(T' u)_ℓ = ∑_{h ∈ ℤ} exp (-π α² (th/s + β_ℓ)²) u_{ℓ+h}`. -/
theorem squareT_apply (hst : s < t) (α : ℝ) (u : ZMod s → ℂ) (ℓ : ZMod s) :
    squareT s t α u ℓ = ∑' h : ℤ,
      (Real.exp (-π * α ^ 2 * ((t : ℝ) * h / s + beta s t ℓ.val) ^ 2) : ℂ) * u (ℓ + h) := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  simp only [squareT, rowSelect, resampT]
  rw [rowIndex_val s t hst ℓ, ← (Equiv.addLeft (ℓ.val : ℤ)).tsum_eq]
  apply tsum_congr
  intro h
  simp only [Equiv.coe_addLeft]
  congr 1
  · rw [rowIndexNat_cast]
    congr 2
    unfold beta frac
    push_cast
    field_simp
    ring
  · congr 1
    push_cast
    simp

/-! ### The diagonal map `D` and the normalisation `N = T' D = 1 + E` -/

/-- `d_ℓ = exp (π α² β_ℓ²)`. -/
noncomputable def dCoef (α : ℝ) (ℓ : ℤ) : ℝ := Real.exp (π * α ^ 2 * beta s t ℓ ^ 2)

omit [NeZero s] [NeZero t] in
theorem one_le_dCoef (α : ℝ) (ℓ : ℤ) : 1 ≤ dCoef s t α ℓ := by
  unfold dCoef
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by positivity)

omit [NeZero s] [NeZero t] in
/-- Inequality (4.1): `d_ℓ ≤ exp (π α² / 4)`. -/
theorem dCoef_le (α : ℝ) (ℓ : ℤ) : dCoef s t α ℓ ≤ Real.exp (π * α ^ 2 / 4) := by
  unfold dCoef
  apply Real.exp_le_exp.mpr
  have := sq_beta_le s t ℓ
  have hπ : 0 ≤ π * α ^ 2 := by positivity
  nlinarith

/-- The diagonal map `D`. -/
noncomputable def diagD (α : ℝ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => (dCoef s t α ℓ.val : ℂ) * u ℓ

/-- `N = T' D`. -/
noncomputable def normN (α : ℝ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  squareT s t α (diagD s t α u)

/-- The exponent of the `h`-th term of `N` at row `ℓ`. -/
noncomputable def normExp (α : ℝ) (ℓ h : ℤ) : ℝ :=
  -π * α ^ 2 * ((t : ℝ) * h / s + beta s t ℓ) ^ 2 + π * α ^ 2 * beta s t (ℓ + h) ^ 2

/-- `E = N - 1`, the off-diagonal part. -/
noncomputable def offDiag (α : ℝ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => ∑' h : ℤ, (if h = 0 then 0 else (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h))

omit [NeZero s] [NeZero t] in
theorem normExp_le (α : ℝ) (ℓ h : ℤ) :
    normExp s t α ℓ h ≤ -π * α ^ 2 * ((t : ℝ) * h / s + beta s t ℓ) ^ 2 + π * α ^ 2 / 4 := by
  unfold normExp
  have := sq_beta_le s t (ℓ + h)
  have hπ : 0 ≤ π * α ^ 2 := by positivity
  nlinarith

/-- The terms of `N` are summable for every `α > 0`. -/
theorem summable_normN_term {α : ℝ} (hα : 0 < α) (u : ZMod s → ℂ) (ℓ : ZMod s) :
    Summable (fun h : ℤ => (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have hc : 0 < π * α ^ 2 * t ^ 2 / s ^ 2 := by positivity
  refine Summable.of_norm_bounded
    (g := fun h : ℤ => Real.exp (π * α ^ 2 / 4) *
      gauss (π * α ^ 2 * t ^ 2 / s ^ 2) (beta s t ℓ.val * s / t + h) * ∑ k, ‖u k‖)
    (((summable_gauss_int hc _).mul_left _).mul_right _) (fun h => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hg : Real.exp (normExp s t α ℓ.val h) ≤
      Real.exp (π * α ^ 2 / 4) * gauss (π * α ^ 2 * t ^ 2 / s ^ 2) (beta s t ℓ.val * s / t + h) := by
    unfold gauss
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    refine (normExp_le s t α ℓ.val h).trans (le_of_eq ?_)
    field_simp
    ring
  calc Real.exp (normExp s t α ℓ.val h) * ‖u (ℓ + h)‖
      ≤ (Real.exp (π * α ^ 2 / 4) * gauss (π * α ^ 2 * t ^ 2 / s ^ 2)
          (beta s t ℓ.val * s / t + h)) * ∑ k, ‖u k‖ := by
        exact mul_le_mul hg (norm_le_sum_norm u _) (norm_nonneg _)
          (mul_pos (Real.exp_pos _) (gauss_pos _ _)).le

/-- `N = 1 + E`. -/
theorem normN_eq (hst : s < t) {α : ℝ} (hα : 0 < α) (u : ZMod s → ℂ) :
    normN s t α u = u + offDiag s t α u := by
  funext ℓ
  rw [Pi.add_apply]
  unfold normN
  rw [squareT_apply s t hst]
  have hterm : ∀ h : ℤ,
      (Real.exp (-π * α ^ 2 * ((t : ℝ) * h / s + beta s t ℓ.val) ^ 2) : ℂ) *
        diagD s t α u (ℓ + h) =
      (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h) := by
    intro h
    unfold diagD dCoef normExp
    rw [beta_val_add, Real.exp_add]
    push_cast
    ring
  simp_rw [hterm]
  rw [(summable_normN_term s t hα u ℓ).tsum_eq_add_tsum_ite 0]
  unfold offDiag
  congr 1
  have h0 : normExp s t α ℓ.val 0 = 0 := by
    unfold normExp
    simp
  rw [h0]
  simp

/-! ### Lemma 4.6: the off-diagonal part is small -/

omit [NeZero t] in
/-- The termwise exponent inequality: for `h ≠ 0`,
`(th/s + β)² - β'² ≥ 2θ (|h| - 1/2)²` where `θ = t/s - 1`. -/
theorem exponent_ge (hst : s < t) (b b' : ℝ) (hb : |b| ≤ 1 / 2) (hb' : |b'| ≤ 1 / 2)
    (h : ℤ) (hh : h ≠ 0) :
    2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 ≤ ((t : ℝ) * h / s + b) ^ 2 - b' ^ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hx : (1 : ℝ) ≤ (t : ℝ) / s := by
    rw [le_div_iff₀ hs, one_mul]
    exact_mod_cast hst.le
  have hm : (1 : ℝ) ≤ |(h : ℝ)| := by
    have := Int.one_le_abs hh
    exact_mod_cast this
  set x : ℝ := (t : ℝ) / s with hxdef
  set m : ℝ := |(h : ℝ)| with hmdef
  have hxh : (t : ℝ) * h / s = x * h := by
    rw [hxdef]
    ring
  rw [hxh]
  -- `|x h + b| ≥ x m - 1/2 ≥ 0`
  have habs : x * m - 1 / 2 ≤ |x * h + b| := by
    have h1 : |x * h + b| ≥ |x * h| - |b| := by
      have := abs_sub_abs_le_abs_sub (x * h) (-b)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    have h2 : |x * (h : ℝ)| = x * m := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < x)]
    have hb2 : |b| ≤ 1 / 2 := hb
    linarith
  have hpos : 0 ≤ x * m - 1 / 2 := by nlinarith
  have hsq : (x * m - 1 / 2) ^ 2 ≤ (x * h + b) ^ 2 := by
    rw [← sq_abs (x * h + b)]
    gcongr
  have hb'2 : b' ^ 2 ≤ 1 / 4 := by
    have h2 : |b'| ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    rw [sq_abs] at h2
    linarith
  -- The algebraic core, with `y = m - 1/2 ≥ 1/2` and `θ = x - 1 ≥ 0`.
  have hy : 1 / 2 ≤ m - 1 / 2 := by linarith
  have hθ : 0 ≤ x - 1 := by linarith
  have hid : (x * m - 1 / 2) ^ 2 - 1 / 4 - 2 * (x - 1) * (m - 1 / 2) ^ 2 =
      ((m - 1 / 2) ^ 2 - 1 / 4) + (x - 1) ^ 2 * (m - 1 / 2) ^ 2 + (x - 1) * (m - 1 / 2) +
        (x - 1) ^ 2 * (m - 1 / 2) + (x - 1) ^ 2 / 4 := by ring
  have h1 : 0 ≤ (m - 1 / 2) ^ 2 - 1 / 4 := by nlinarith
  have h2 : 0 ≤ (x - 1) ^ 2 * (m - 1 / 2) ^ 2 := by positivity
  have h3 : 0 ≤ (x - 1) * (m - 1 / 2) := by positivity
  have h4 : 0 ≤ (x - 1) ^ 2 * (m - 1 / 2) := by positivity
  have h5 : 0 ≤ (x - 1) ^ 2 / 4 := by positivity
  nlinarith

/-- For integers `m ≥ 1`, `(m - 1/2)² ≥ 1/4 + 2 (m - 1)`. -/
theorem sq_sub_half_ge (m : ℕ) (hm : 1 ≤ m) :
    1 / 4 + 2 * ((m : ℝ) - 1) ≤ ((m : ℝ) - 1 / 2) ^ 2 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this
    norm_num
  · have h2 : (2 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith

omit [NeZero t] in
/-- Each off-diagonal term is bounded by `A q^{|h| - 1}` with
`A = exp (-π α² θ / 2)` and `q = exp (-4 π α² θ)`. -/
theorem offDiag_term_le (hst : s < t) {α : ℝ} (hα : 0 < α) (u : ZMod s → ℂ)
    (hu : ∀ j, ‖u j‖ ≤ 1) (ℓ : ZMod s) (h : ℤ) (hh : h ≠ 0) :
    ‖(Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤
      Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2) *
        Real.exp (-4 * π * α ^ 2 * ((t : ℝ) / s - 1)) ^ (h.natAbs - 1) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hθ : 0 ≤ (t : ℝ) / s - 1 := by
    rw [sub_nonneg, le_div_iff₀ hs, one_mul]
    exact_mod_cast hst.le
  have hπ : 0 ≤ π * α ^ 2 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (normExp s t α ℓ.val h) * ‖u (ℓ + h)‖
      ≤ Real.exp (normExp s t α ℓ.val h) * 1 := by
        gcongr
        exact hu _
    _ = Real.exp (normExp s t α ℓ.val h) := mul_one _
    _ ≤ _ := ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm1 : 1 ≤ h.natAbs := Int.natAbs_pos.mpr hh
  have hcast : ((h.natAbs - 1 : ℕ) : ℝ) = |(h : ℝ)| - 1 := by
    rw [Nat.cast_sub hm1, Nat.cast_natAbs, Int.cast_abs]
    push_cast
    ring
  have hsq := sq_sub_half_ge h.natAbs hm1
  rw [Nat.cast_natAbs, Int.cast_abs] at hsq
  have hexp := exponent_ge s t hst (beta s t ℓ.val) (beta s t (ℓ.val + h))
    (abs_beta_le s t _) (abs_beta_le s t _) h hh
  unfold normExp
  rw [hcast]
  set θ : ℝ := (t : ℝ) / s - 1
  set y : ℝ := |(h : ℝ)| - 1 / 2
  have hπθ : 0 ≤ π * α ^ 2 * θ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hexp hπ, mul_le_mul_of_nonneg_left hsq hπθ]

/-- The comparison series `g h = A q^{|h|-1}` (and `0` at `h = 0`) sums to `2 A / (1 - q)`. -/
theorem hasSum_comparison (A q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun h : ℤ => if h = 0 then 0 else A * q ^ (h.natAbs - 1))
      (A * (1 - q)⁻¹ + A * (1 - q)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · refine (hasSum_nat_add_iff' 1).mp ?_
    convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left A using 1
    · funext n
      split_ifs with h
      · omega
      · congr 2
    · simp
  · convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left A using 1
    funext n
    split_ifs with h
    · omega
    · congr 2

/-- `exp 12 ≥ 625`, enough to make the geometric tail negligible. -/
theorem exp_twelve_ge : (625 : ℝ) ≤ Real.exp 12 := by
  have h6 : (25 : ℝ) ≤ Real.exp 6 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num)
    norm_num at this
    linarith
  have : Real.exp 12 = Real.exp 6 * Real.exp 6 := by
    rw [← Real.exp_add]
    norm_num
  rw [this]
  nlinarith

omit [NeZero t] in
/-- Lemma 4.6 of Harvey and van der Hoeven: entrywise,
`‖E u‖ ≤ 2.01 exp (-π α² θ / 2)` for `‖u‖ ≤ 1` when `α² θ ≥ 1`. -/
theorem norm_offDiag_le (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ‖ ≤ 2.01 * Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2) := by
  set θ : ℝ := (t : ℝ) / s - 1 with hθdef
  set A : ℝ := Real.exp (-π * α ^ 2 * θ / 2) with hA
  set q : ℝ := Real.exp (-4 * π * α ^ 2 * θ) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq]
    have := Real.exp_lt_exp.mpr (show -4 * π * α ^ 2 * θ < 0 by
      have := Real.pi_pos
      nlinarith)
    simpa using this
  -- `q ≤ exp (-12) ≤ 1/625`
  have hq625 : q ≤ 1 / 625 := by
    have h1 : q ≤ Real.exp (-12) := by
      rw [hq]
      apply Real.exp_le_exp.mpr
      have := Real.pi_gt_three
      nlinarith
    have h2 : Real.exp (-12) ≤ 1 / 625 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) exp_twelve_ge
    linarith
  have hsum := hasSum_comparison A q hq0 hq1
  have hbound : ‖offDiag s t α u ℓ‖ ≤ A * (1 - q)⁻¹ + A * (1 - q)⁻¹ := by
    unfold offDiag
    refine tsum_of_norm_bounded hsum (fun h => ?_)
    by_cases hh : h = 0
    · simp [hh]
    · simp only [hh, ↓reduceIte]
      exact offDiag_term_le s t hst hα u hu ℓ h hh
  have hA0 : 0 < A := Real.exp_pos _
  have h1q : 0 < 1 - q := by linarith
  calc ‖offDiag s t α u ℓ‖ ≤ A * (1 - q)⁻¹ + A * (1 - q)⁻¹ := hbound
    _ = 2 * A / (1 - q) := by ring
    _ ≤ 2.01 * A := by
        rw [div_le_iff₀ h1q]
        nlinarith

/-- `exp (π / 2) ≥ 4.38`. -/
theorem exp_half_pi_ge : (4.38 : ℝ) ≤ Real.exp (π / 2) := by
  have hπ := Real.pi_gt_d2
  have hq : 1 + π / 4 + (π / 4) ^ 2 / 2 ≤ Real.exp (π / 4) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have h2 : Real.exp (π / 2) = Real.exp (π / 4) * Real.exp (π / 4) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h2]
  have hlow : (2.093 : ℝ) ≤ 1 + π / 4 + (π / 4) ^ 2 / 2 := by nlinarith
  nlinarith

omit [NeZero t] in
/-- Under the hypothesis of Lemma 4.6, `‖E u‖ ≤ 1/2` entrywise. -/
theorem norm_offDiag_le_half (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (ℓ : ZMod s) : ‖offDiag s t α u ℓ‖ ≤ 1 / 2 := by
  refine (norm_offDiag_le s t hst hα hθ u hu ℓ).trans ?_
  have h1 : Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2) ≤ Real.exp (-(π / 2)) := by
    apply Real.exp_le_exp.mpr
    have := Real.pi_pos
    nlinarith
  have h2 : Real.exp (-(π / 2)) ≤ 1 / 4.38 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_half_pi_ge
  calc 2.01 * Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2)
      ≤ 2.01 * (1 / 4.38) := by gcongr; linarith
    _ ≤ 1 / 2 := by norm_num

end Setup

end IntegerMultBounds.NLogN
