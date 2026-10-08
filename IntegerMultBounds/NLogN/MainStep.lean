import IntegerMultBounds.NLogN.MainReduction
import IntegerMultBounds.NLogN.CRTMulti
import IntegerMultBounds.NLogN.Section5Approx
import IntegerMultBounds.NLogN.ResamplingMulti
import IntegerMultBounds.NLogN.MainParams

/-! The recursive step of Harvey–van der Hoeven (Proposition 5.4), assembled
at the vector level with the transform approximation as a hypothesis. Proved:
the normalized `d`-dimensional transform `F` on the Chinese-remainder grid of
pairwise coprime lengths `s_i`, with `S = ∏ s_i`, satisfies `‖F‖ ≤ 1`, its
composition with index negation `F⁻` is a contraction, and the normalized
convolution `(u ∗ v) / S` equals `S · F⁻(F u · F v)`, the paper's `w = S w₀`.
Given numerical approximations of `F` and `F⁻` with scaled errors `ε_F`, `ε_I`
that keep the unit ball, the forward, rounded pointwise, inverse pipeline on
the scaled digit grids, rescaled by `S`, is within `S (ε_I + 2 ε_F + 2)` scaled
units of the normalized convolution, and once `2^(2k) S² (ε_I + 2 ε_F + 2)` is
below `2^(p−1)` the rounded output evaluates to the exact product of the two
input bit strings. Constructing the transform approximation (Proposition
5.2), discharging the precision condition from its error bound and the
parameter inequalities, the data rearrangement cost, and all tape costs are
not here. -/

open Real Complex

namespace IntegerMultBounds.NLogN

variable {d : ℕ} {s : Fin d → ℕ} [∀ i, NeZero (s i)]

/-- The transform composed with index negation, the normalized inverse
transform up to the factor `S`. -/
noncomputable def negF (s : Fin d → ℕ) [∀ i, NeZero (s i)]
    (u : ((i : Fin d) → ZMod (s i)) → ℂ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  fun k => dftDCLM s u (-k)

/-- Index negation as an operator. -/
noncomputable def negCLM (s : Fin d → ℕ) [∀ i, NeZero (s i)] :
    (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (-k)

theorem negCLM_apply (u : ((i : Fin d) → ZMod (s i)) → ℂ) (k : (i : Fin d) → ZMod (s i)) :
    negCLM s u k = u (-k) := rfl

theorem opNorm_negCLM_le : ‖negCLM s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  rw [negCLM_apply]
  exact norm_le_pi_norm u (-k)

/-- `F⁻` as an operator. -/
noncomputable def negFCLM (s : Fin d → ℕ) [∀ i, NeZero (s i)] :
    (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ) :=
  negCLM s ∘L dftDCLM s

theorem negFCLM_apply (u : ((i : Fin d) → ZMod (s i)) → ℂ) : negFCLM s u = negF s u := rfl

theorem opNorm_dftDCLM_le : ‖dftDCLM s‖ ≤ 1 := by
  rw [dftDCLM_eq_tensor]
  exact opNorm_tensorRCLM_le _ fun i => opNorm_dftCLM_le

theorem opNorm_negFCLM_le : ‖negFCLM s‖ ≤ 1 := by
  calc ‖negFCLM s‖ ≤ ‖negCLM s‖ * ‖dftDCLM s‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by gcongr; exacts [opNorm_negCLM_le, opNorm_dftDCLM_le]
    _ = 1 := one_mul _

/-! ### The exact identity -/

theorem dftD_smul {R : Type*} [CommRing R] {N : Fin d → ℕ} [∀ i, NeZero (N i)]
    (ζ : Fin d → R) (c : R) (a : ((i : Fin d) → ZMod (N i)) → R) :
    dftD ζ (fun j => c * a j) = fun k => c * dftD ζ a k := by
  funext k
  simp only [dftD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The roots used by `dftDCLM` are primitive. -/
theorem isPrimitiveRoot_inv_exp (i : Fin d) :
    IsPrimitiveRoot (Complex.exp (2 * π * I / (s i)))⁻¹ (s i) :=
  (Complex.isPrimitiveRoot_exp (s i) (NeZero.ne _)).inv

theorem cast_prod_ne_zero : ((∏ i, s i : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NeZero.ne _)

/-- `F (a ∗ b) = S · (F a · F b)`. -/
theorem dftDCLM_convG (a b : ((i : Fin d) → ZMod (s i)) → ℂ) :
    dftDCLM s (convG a b) = fun k => ((∏ i, s i : ℕ) : ℂ) * (dftDCLM s a k * dftDCLM s b k) := by
  funext k
  simp only [dftDCLM_apply]
  rw [dftD_convG isPrimitiveRoot_inv_exp]
  have hS := cast_prod_ne_zero (s := s)
  field_simp

/-- `F⁻ (F c) = c / S`. -/
theorem negF_dftDCLM (c : ((i : Fin d) → ZMod (s i)) → ℂ) :
    negF s (dftDCLM s c) = fun k => (1 / ((∏ i, s i : ℕ) : ℂ)) * c k := by
  funext k
  simp only [negF, dftDCLM_apply, dftD_smul, dftD_dftD isPrimitiveRoot_inv_exp, neg_neg]
  have hS := cast_prod_ne_zero (s := s)
  rw [← Nat.cast_prod]
  field_simp

theorem dftDCLM_mul (c : ℂ) (f : ((i : Fin d) → ZMod (s i)) → ℂ) :
    dftDCLM s (fun k => c * f k) = fun k => c * dftDCLM s f k := by
  show dftDCLM s (c • f) = c • dftDCLM s f
  exact map_smul _ _ _

/-- The normalized convolution is `S · F⁻ (F a · F b)`, the paper's `w = S w₀`. -/
theorem convG_div_eq_negF (a b : ((i : Fin d) → ZMod (s i)) → ℂ) :
    (fun k => convG a b k / ((∏ i, s i : ℕ) : ℂ)) =
      fun k => ((∏ i, s i : ℕ) : ℂ) * negF s (pw (dftDCLM s a) (dftDCLM s b)) k := by
  have hS := cast_prod_ne_zero (s := s)
  have h1 : pw (dftDCLM s a) (dftDCLM s b) =
      fun k => (1 / ((∏ i, s i : ℕ) : ℂ)) * dftDCLM s (convG a b) k := by
    funext k
    rw [dftDCLM_convG]
    simp only [pw]
    field_simp
  rw [h1, ← dftDCLM_mul, negF_dftDCLM]
  funext k
  field_simp

/-! ### The approximate convolution on the grid -/

/-- The grid vector of the `2^(-k)`-scaled digit list. -/
noncomputable def digitGrid (hs : Pairwise (Function.onFun Nat.Coprime s)) (k : ℕ)
    (ds : List ℕ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  toGridD hs fun j => vecZ (∏ i, s i) ds j / 2 ^ k

theorem norm_digitGrid_le (hs : Pairwise (Function.onFun Nat.Coprime s)) {k : ℕ} (hk : 0 < k)
    (x : List Bool) : ‖digitGrid hs k (digitsOf k x)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  simp only [digitGrid, toGridD, Function.comp_apply, vecZ, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_ofNat]
  have h := getD_lt (digitsOf_lt hk x) (by positivity)
    ((ZMod.prodEquivPi s hs).symm j).val
  rw [div_le_one (by positivity)]
  exact_mod_cast h.le

/-- The paper's normalized convolution of the digit vectors, on the grid. -/
theorem scaledConv_eq_grid (hs : Pairwise (Function.onFun Nat.Coprime s)) (k : ℕ)
    (dx dy : List ℕ) :
    scaledConv (∏ i, s i) k dx dy = ofGridD hs fun j =>
      ((∏ i, s i : ℕ) : ℂ) * negF s (pw (dftDCLM s (digitGrid hs k dx))
        (dftDCLM s (digitGrid hs k dy))) j := by
  rw [← convG_div_eq_negF]
  funext i
  simp only [scaledConv, ofGridD, Function.comp_apply]
  congr 1
  have := congrFun (toGridD_cconv hs (fun j => vecZ (∏ i, s i) dx j / 2 ^ k)
    (fun j => vecZ (∏ i, s i) dy j / 2 ^ k)) (ZMod.prodEquivPi s hs i)
  simp only [digitGrid]
  rw [← this]
  simp [toGridD]

/-- The approximate normalized convolution of two digit lists, rescaled by `S`. -/
noncomputable def approxConvS (hs : Pairwise (Function.onFun Nat.Coprime s)) (p k : ℕ)
    (F' Fi' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ))
    (dx dy : List ℕ) : ZMod (∏ i, s i) → ℂ :=
  fun i => ((∏ i, s i : ℕ) : ℂ) *
    ofGridD hs (convVia p F' Fi' (digitGrid hs k dx) (digitGrid hs k dy)) i

/-- Proposition 5.3 on the digit grids: the rescaled pipeline is within
`S (ε_I + 2 ε_F + 2)` scaled units of the normalized convolution. -/
theorem approxConvS_err (hs : Pairwise (Function.onFun Nat.Coprime s)) {p k : ℕ} (hk : 0 < k)
    {F' Fi' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)}
    {εF εI : ℝ} (hF' : ApproxMap p F' (dftDCLM s) εF) (hFi' : ApproxMap p Fi' (negFCLM s) εI)
    (hF'ball : ∀ u, ‖u‖ ≤ 1 → ‖F' u‖ ≤ 1) (x y : List Bool) (i : ZMod (∏ i, s i)) :
    (2 : ℝ) ^ p * ‖approxConvS hs p k F' Fi' (digitsOf k x) (digitsOf k y) i -
      scaledConv (∏ i, s i) k (digitsOf k x) (digitsOf k y) i‖ ≤
      (∏ i, s i : ℕ) * (εI + (2 * εF + 2)) := by
  rw [scaledConv_eq_grid hs]
  simp only [approxConvS, ofGridD, Function.comp_apply]
  rw [← mul_sub, norm_mul, Complex.norm_natCast]
  have h := prop53_err opNorm_dftDCLM_le opNorm_negFCLM_le hF' hFi' hF'ball
    (norm_digitGrid_le hs hk x) (norm_digitGrid_le hs hk y)
  rw [negFCLM_apply] at h
  set j := ZMod.prodEquivPi s hs i
  have hj : ‖convVia p F' Fi' (digitGrid hs k (digitsOf k x)) (digitGrid hs k (digitsOf k y)) j -
      negF s (pw (dftDCLM s (digitGrid hs k (digitsOf k x)))
        (dftDCLM s (digitGrid hs k (digitsOf k y)))) j‖ ≤
      ‖convVia p F' Fi' (digitGrid hs k (digitsOf k x)) (digitGrid hs k (digitsOf k y)) -
      negF s (pw (dftDCLM s (digitGrid hs k (digitsOf k x)))
        (dftDCLM s (digitGrid hs k (digitsOf k y))))‖ := by
    have := norm_le_pi_norm (convVia p F' Fi' (digitGrid hs k (digitsOf k x))
      (digitGrid hs k (digitsOf k y)) - negF s (pw (dftDCLM s (digitGrid hs k (digitsOf k x)))
        (dftDCLM s (digitGrid hs k (digitsOf k y))))) j
    simpa using this
  calc (2 : ℝ) ^ p * ((∏ i, s i : ℕ) * ‖_‖)
      = (∏ i, s i : ℕ) * (2 ^ p * ‖_‖) := by ring
    _ ≤ (∏ i, s i : ℕ) * (2 ^ p * ‖convVia p F' Fi' (digitGrid hs k (digitsOf k x))
          (digitGrid hs k (digitsOf k y)) - negF s (pw (dftDCLM s (digitGrid hs k (digitsOf k x)))
          (dftDCLM s (digitGrid hs k (digitsOf k y))))‖) := by gcongr
    _ ≤ (∏ i, s i : ℕ) * (εI + (2 * εF + 2)) := by gcongr

/-! ### The recursive step -/

/-- The recursive step: with transform approximations of scaled errors
`ε_F`, `ε_I` and enough precision, the rounded, rescaled pipeline output
evaluates to the exact product. -/
theorem main_step (hs : Pairwise (Function.onFun Nat.Coprime s)) {p k : ℕ} (hk : 0 < k)
    {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ (∏ i, s i) + 1)
    {F' Fi' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)}
    {εF εI : ℝ} (hF' : ApproxMap p F' (dftDCLM s) εF) (hFi' : ApproxMap p Fi' (negFCLM s) εI)
    (hF'ball : ∀ u, ‖u‖ ≤ 1 → ‖F' u‖ ≤ 1)
    (hprec : (2 : ℝ) ^ (2 * k) * (∏ i, s i : ℕ) * ((∏ i, s i : ℕ) * (εI + (2 * εF + 2))) <
      2 ^ p / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * k) * (∏ i, s i : ℕ)) *
        approxConvS hs p k F' Fi' (digitsOf k x) (digitsOf k y) (i.val : ZMod (∏ i, s i))).re).toNat)
      = Machine.binaryValue x * Machine.binaryValue y := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set ε : ℝ := (∏ i, s i : ℕ) * (εI + (2 * εF + 2))
  refine product_from_approx hk hS (δ := ε / 2 ^ p) ?_ ?_
  · intro i
    rw [le_div_iff₀ hp, mul_comm]
    exact approxConvS_err hs hk hF' hFi' hF'ball x y i
  · rw [← mul_div_assoc, div_lt_iff₀ hp]
    linarith

end IntegerMultBounds.NLogN
