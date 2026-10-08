import IntegerMultBounds.NLogN.ResamplingMultiNumeric
import IntegerMultBounds.NLogN.Section5Approx
import IntegerMultBounds.NLogN.MainStep
import IntegerMultBounds.NLogN.PrecisionCheck

/-! Proposition 5.2 of Harvey–van der Hoeven and its use in the recursive step.
Proved: the numerical prime-grid transform `2^γ B̃ F̃_t Ã` approximates the
normalized `d`-dimensional transform `F_s` with scaled error
`2^γ (d ε_B + ε_{F_t} + d ε_A)`, and its index negation approximates `F⁻`
with the same error; with `ε_A, ε_B ≤ p²`, `ε_{F_t} ≤ 8 T log₂ T`, and
`d p² ≤ 4 T log₂ T` (which the parameter choices imply) the error is at most
`2^(γ+5) T log₂ T`; the parameter slack `γ + 2d + 14 < b` holds, so the
precision condition of `main_step` is met with the exponent `γ + 2d` that
the explicit factorization produces; and hence the recursive step returns
the exact product given only an approximation of the power-of-two transform
`F̃_t` and the per-coordinate numerical resampling maps. The power-of-two
transform's approximation, the choice of primes `s_i` with `α² θ_i ≥ 1`, and
all costs remain hypotheses or are not modeled. -/

open Real

namespace IntegerMultBounds.NLogN

section Transform

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ} {p : ℕ}

/-- Proposition 5.2: the numerical prime-grid transform `2^γ B̃ F̃_t Ã` approximates
`F_s` with scaled error `2^γ (d ε_B + ε_{F_t} + d ε_A)`. -/
theorem mainTransform_approx (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1))
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) α) = 1)
    (A' : (i : Fin d) → (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ))
    (B' : (i : Fin d) → (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ)) {εA εB εFt : ℝ}
    (hA' : ∀ i, ApproxMap p (A' i) (resampA (s i) (t i) α) εA)
    (hB' : ∀ i, ApproxMap p (B' i) (resampB (s i) (t i) α (hcop i) (J i)) εB)
    (hA'ball : ∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) (hB'ball : ∀ i v, ‖v‖ ≤ 1 → ‖B' i v‖ ≤ 1)
    (Ft' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ))
    (hFt : ApproxMap p Ft' (dftDCLM t) εFt) (hFt'ball : ∀ u, ‖u‖ ≤ 1 → ‖Ft' u‖ ≤ 1) :
    ApproxMap p (fun v => ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
        tensorZR d t s B' (Ft' (tensorZR d s t A' v)))
      (dftDCLM s) (2 ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * (d * εB + εFt + d * εA)) := by
  obtain ⟨hfac, hA, hB⟩ :=
    resampling_multi_numeric hst hcop hα hθ J hJ A' B' hA' hB' hA'ball hB'ball
  have hBn : ‖tensorRCLM (fun i => resampB (s i) (t i) α (hcop i) (J i))‖ ≤ 1 :=
    opNorm_tensorRCLM_le _ fun i =>
      (resampling_factorization_explicit (hst i) (hcop i) hα (hθ i) (J i) (hJ i)).2.2
  exact prop52 hBn opNorm_dftDCLM_le hA hFt hB (tensorZR_ball d s t A' hA'ball) hFt'ball hfac

/-- Index negation of a vector, the exact data move behind the inverse transform. -/
def negVec {ι : Type*} [Neg ι] (u : ι → ℂ) : ι → ℂ := fun k => u (-k)

/-- The index negation of any approximation of `F` approximates `F⁻` with the same
error. -/
theorem approxMap_negVec
    {F' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)} {ε : ℝ}
    (hF' : ApproxMap p F' (dftDCLM s) ε) :
    ApproxMap p (fun v => negVec (F' v)) (negFCLM s) ε := by
  intro v hv
  refine le_trans ?_ (hF' v hv)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  exact norm_le_pi_norm (F' v - dftDCLM s v) (-k)

end Transform

/-! ### The paper's numeric bound -/

/-- With `ε_A, ε_B ≤ p²`, `ε_{F_t} ≤ 8 T L`, and `d p² ≤ 4 T L`, the transform error is
at most `2^(γ+4) T L`. -/
theorem error_bound {d γ : ℕ} {εA εB εFt T L p : ℝ} (hεA : εA ≤ p ^ 2) (hεB : εB ≤ p ^ 2)
    (hεFt : εFt ≤ 8 * T * L) (hdp : (d : ℝ) * p ^ 2 ≤ 4 * T * L) :
    (2 : ℝ) ^ γ * (d * εB + εFt + d * εA) ≤ 2 ^ (γ + 4) * T * L := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (d : ℝ) * εB ≤ d * p ^ 2 := mul_le_mul_of_nonneg_left hεB hd0
  have h2 : (d : ℝ) * εA ≤ d * p ^ 2 := mul_le_mul_of_nonneg_left hεA hd0
  calc (2 : ℝ) ^ γ * (d * εB + εFt + d * εA)
      ≤ 2 ^ γ * (16 * (T * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 2 ^ (γ + 4) * T * L := by rw [pow_add]; ring

/-- `b³ ≤ 2^(b−2)` for `b ≥ 16`. -/
theorem cube_le_two_pow {b : ℕ} (hb : 16 ≤ b) : b ^ 3 ≤ 2 ^ (b - 2) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    have h16 : 16 * b ^ 2 ≤ b ^ 3 := by
      rw [show b ^ 3 = b * b ^ 2 by ring]; exact Nat.mul_le_mul_right _ hb
    have h1 : (b + 1) ^ 3 ≤ 2 * b ^ 3 := by nlinarith
    have h2 : 2 ^ (b + 1 - 2) = 2 * 2 ^ (b - 2) := by
      rw [show b + 1 - 2 = (b - 2) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc (b + 1) ^ 3 ≤ 2 * b ^ 3 := h1
      _ ≤ 2 * 2 ^ (b - 2) := Nat.mul_le_mul_left _ ih

/-- The parameter fact behind Proposition 5.2: `d p² ≤ 4 T log₂ T`. -/
theorem d_p_sq_le_nat {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    d * precision n ^ 2 ≤ 4 * transformSize n * Nat.log 2 (transformSize n) := by
  have hb := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n :=
    le_trans (by calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (d ^ 12) :=
                    Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))) hn
  have hT4 := (transformSize_bounds hn2).1
  have h2b := two_pow_chunk_lt hn2
  have hTge := transformSize_ge hd hn
  have hlog : 2 * d ≤ Nat.log 2 (transformSize n) := by
    rw [log_transformSize]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by unfold transformSize at hTge; exact hTge)
  set b := chunkSize n with hb'
  set T := transformSize n with hT'
  set L := Nat.log 2 T with hL'
  have hcube := cube_le_two_pow (b := b) (by omega)
  have h2bb : 2 ^ b = 4 * 2 ^ (b - 2) := by
    rw [show b = (b - 2) + 2 by omega, pow_add]
    simp only [Nat.add_sub_cancel]
    ring
  -- `9 b³ ≤ 2 T b`.
  have h9 : 9 * b ^ 3 ≤ 2 * T * b := by
    calc 9 * b ^ 3 ≤ 9 * 2 ^ (b - 2) := Nat.mul_le_mul_left _ hcube
      _ ≤ 16 * 2 ^ (b - 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 4 * 2 ^ b := by rw [h2bb]; ring
      _ ≤ 8 * n := by omega
      _ ≤ 2 * T * b := by rw [mul_assoc]; omega
  have h9' : 9 * b ^ 2 ≤ 2 * T := by
    have : 9 * b ^ 2 * b ≤ 2 * T * b := by rw [show 9 * b ^ 2 * b = 9 * b ^ 3 by ring]; exact h9
    exact Nat.le_of_mul_le_mul_right this (by omega)
  calc d * precision n ^ 2 = d * (36 * b ^ 2) := by rw [precision]; ring
    _ ≤ d * (8 * T) := Nat.mul_le_mul_left _ (by omega)
    _ = 4 * T * (2 * d) := by ring
    _ ≤ 4 * T * L := Nat.mul_le_mul_left _ hlog

theorem d_p_sq_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    (d : ℝ) * (precision n : ℝ) ^ 2 ≤
      4 * (transformSize n : ℝ) * (Nat.log 2 (transformSize n) : ℝ) := by
  exact_mod_cast d_p_sq_le_nat hd hn

/-! ### Parameter slack for the explicit factorization exponent -/

/-- `γ + 2d + 14 < b`: the explicit factorization's exponent `γ + 2d` still leaves the
slack the precision condition needs. -/
theorem gammaParam_two_d_add_lt {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    gammaParam d n + 2 * d + 14 < chunkSize n := by
  have hb := chunkSize_ge_4096 hd hn
  have hd12 := chunkSize_ge hn
  have h22 := alphaParam_ge_22 hd hb
  have hlt := alphaParam_pred_pow_lt (d := d) (n := n) (by positivity)
  unfold gammaParam
  set a := alphaParam d n with ha
  set b := chunkSize n with hb'
  set m := a - 1 with hm
  have ham : a = m + 1 := by omega
  have hm21 : 21 ≤ m := by omega
  have h1 : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
  set γ := 2 * d * a ^ 2 with hγ
  have h2 : γ ≤ 4 * d * m ^ 2 := by rw [hγ, ham]; nlinarith
  have h3 : γ ^ 2 ≤ 16 * d ^ 2 * m ^ 4 := by
    calc γ ^ 2 ≤ (4 * d * m ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 16 * d ^ 2 * m ^ 4 := by ring
  have hdpos : 0 < d ^ 2 := by positivity
  have h4 : 16 * d ^ 2 * m ^ 4 < 16 * d ^ 2 * (12 * d ^ 2 * b) :=
    Nat.mul_lt_mul_of_pos_left hlt (by positivity)
  have h5 : γ ^ 2 < 192 * d ^ 4 * b := by
    calc γ ^ 2 ≤ 16 * d ^ 2 * m ^ 4 := h3
      _ < 16 * d ^ 2 * (12 * d ^ 2 * b) := h4
      _ = 192 * d ^ 4 * b := by ring
  have hD := pow_four_mul_le hd12 hb
  set D := d ^ 4 with hD'
  -- The shift `M := 2d + 14` satisfies `194 M ≤ b`.
  set M := 2 * d + 14 with hM
  have hMb : 194 * M ≤ b := by
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have : d = 2 := by omega
      subst this
      omega
    · have hd4 : 2 * d + 14 ≤ D := by
        rw [hD']
        have h27 : 3 ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hd3 3
        calc 2 * d + 14 ≤ 27 * d := by omega
          _ = d * 3 ^ 3 := by ring
          _ ≤ d * d ^ 3 := Nat.mul_le_mul_left _ h27
          _ = d ^ 4 := by ring
      omega
  obtain ⟨c, hc⟩ : ∃ c, b = c + M := ⟨b - M, by omega⟩
  have h6 : 194 * (192 * D * b) ≤ 192 * b * b := by
    calc 194 * (192 * D * b) = 192 * b * (194 * D) := by ring
      _ ≤ 192 * b * b := Nat.mul_le_mul_left _ hD
  have h7 : 192 * b * b ≤ 194 * c ^ 2 := by
    rw [hc]
    have hcM : 194 * M ≤ c + M := by rw [← hc]; exact hMb
    nlinarith
  have h8 : 194 * γ ^ 2 < 194 * c ^ 2 := by
    calc 194 * γ ^ 2 < 194 * (192 * D * b) := by omega
      _ ≤ 192 * b * b := h6
      _ ≤ 194 * c ^ 2 := h7
  have h9 : γ ^ 2 < c ^ 2 := by omega
  have h10 : γ < c := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h9
  omega

/-- The precision condition for an arbitrary error exponent `γ'` with `γ' + 11 < b`. -/
theorem precision_ok_gen_nat {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (S : ℕ)
    (hS : S ≤ transformSize n) (γ' : ℕ) (hγ' : γ' + 11 < chunkSize n) (ε : ℕ)
    (hε : ε ≤ 2 ^ (γ' + 5) * transformSize n * Nat.log 2 (transformSize n)) :
    2 ^ (2 * chunkSize n) * S * (S * (3 * ε + 2)) * 2 < 2 ^ precision n := by
  have hb := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n :=
    le_trans (by calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (d ^ 12) :=
                    Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))) hn
  have hL := log_transformSize_le hn2 (by omega)
  have hTb := (transformSize_bounds hn2).2
  have hT : transformSize n < 2 ^ chunkSize n :=
    lt_of_lt_of_le (transformSize_lt hn2 (by omega)) (n_le_two_pow_chunk n)
  set b := chunkSize n with hb'
  set T := transformSize n with hT'
  have hTL : T * Nat.log 2 T < 2 ^ (b + 3) := by
    calc T * Nat.log 2 T ≤ T * b := Nat.mul_le_mul_left _ hL
      _ < 8 * n := hTb
      _ ≤ 8 * 2 ^ b := Nat.mul_le_mul_left _ (n_le_two_pow_chunk n)
      _ = 2 ^ (b + 3) := by rw [pow_add]; ring
  have hε' : ε ≤ 2 ^ (γ' + b + 8) := by
    calc ε ≤ 2 ^ (γ' + 5) * T * Nat.log 2 T := hε
      _ = 2 ^ (γ' + 5) * (T * Nat.log 2 T) := by ring
      _ ≤ 2 ^ (γ' + 5) * 2 ^ (b + 3) := Nat.mul_le_mul_left _ hTL.le
      _ = 2 ^ (γ' + b + 8) := by rw [← pow_add]; congr 1; ring
  have h3 : 3 * ε + 2 ≤ 2 ^ (γ' + b + 10) := by
    have hP1 : 1 < 2 ^ (γ' + b + 8) := Nat.one_lt_two_pow (by omega)
    have hP2 : 2 ^ (γ' + b + 10) = 4 * 2 ^ (γ' + b + 8) := by
      rw [show γ' + b + 10 = (γ' + b + 8) + 2 by ring, pow_add]; ring
    rw [hP2]
    set P := 2 ^ (γ' + b + 8) with hP
    omega
  have hS' : S ≤ 2 ^ b := le_trans hS hT.le
  calc 2 ^ (2 * b) * S * (S * (3 * ε + 2)) * 2
      ≤ 2 ^ (2 * b) * 2 ^ b * (2 ^ b * 2 ^ (γ' + b + 10)) * 2 :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hS') (Nat.mul_le_mul hS' h3))
    _ = 2 ^ (5 * b + γ' + 11) := by
        rw [show 5 * b + γ' + 11 = 2 * b + b + (b + (γ' + b + 10)) + 1 by ring]
        simp only [pow_add, pow_one]
    _ < 2 ^ (6 * b) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = 2 ^ precision n := by rw [precision]

/-- The precision condition of `main_step` with the error exponent `γ + 2d` of the
explicit factorization. -/
theorem precision_ok_gen {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (S : ℕ)
    (hS : S ≤ transformSize n) {εF εI : ℝ}
    (hεF : εF ≤ 2 ^ (gammaParam d n + 2 * d + 5) * transformSize n *
      Nat.log 2 (transformSize n))
    (hεI : εI ≤ 2 ^ (gammaParam d n + 2 * d + 5) * transformSize n *
      Nat.log 2 (transformSize n)) :
    (2 : ℝ) ^ (2 * chunkSize n) * S * (S * (εI + (2 * εF + 2))) < 2 ^ precision n / 2 := by
  have hγ := gammaParam_two_d_add_lt hd hn
  set E : ℕ := 2 ^ (gammaParam d n + 2 * d + 5) * transformSize n *
    Nat.log 2 (transformSize n) with hE
  have hnat := precision_ok_gen_nat hd hn S hS (gammaParam d n + 2 * d) (by omega) E le_rfl
  set X : ℕ := 2 ^ (2 * chunkSize n) * S * (S * (3 * E + 2)) with hX
  have hEr : (2 : ℝ) ^ (gammaParam d n + 2 * d + 5) * transformSize n *
      Nat.log 2 (transformSize n) = (E : ℝ) := by rw [hE]; push_cast; ring
  rw [hEr] at hεF hεI
  have h1 : εI + (2 * εF + 2) ≤ 3 * (E : ℝ) + 2 := by linarith
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (2 * chunkSize n) * S * (S * (εI + (2 * εF + 2))) ≤ (X : ℝ) := by
    rw [hX]; push_cast
    gcongr
  have h3 : (X : ℝ) * 2 < 2 ^ precision n := by exact_mod_cast hnat
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-! ### The recursive step with the paper's parameters -/

section Step

variable {d : ℕ} {s : Fin d → ℕ} [∀ i, NeZero (s i)]

/-- The recursive step with the paper's parameters: chunk size `b`, precision `6b`, a
coprime grid with `S ≤ T < 2S`, and transform approximations with the paper's error
bound (exponent `γ + 2d`). -/
theorem main_step_params {n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hS : ∏ i, s i ≤ transformSize n) (hS2 : transformSize n < 2 * ∏ i, s i)
    {F' Fi' : (((i : Fin d) → ZMod (s i)) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ)}
    {εF εI : ℝ} (hF' : ApproxMap (precision n) F' (dftDCLM s) εF)
    (hFi' : ApproxMap (precision n) Fi' (negFCLM s) εI)
    (hF'ball : ∀ u, ‖u‖ ≤ 1 → ‖F' u‖ ≤ 1)
    (hεF : εF ≤ 2 ^ (gammaParam d n + 2 * d + 5) * transformSize n *
      Nat.log 2 (transformSize n))
    (hεI : εI ≤ 2 ^ (gammaParam d n + 2 * d + 5) * transformSize n *
      Nat.log 2 (transformSize n)) :
    evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
        approxConvS hs (precision n) (chunkSize n) F' Fi' (digitsOf (chunkSize n) x)
          (digitsOf (chunkSize n) y) (i.val : ZMod (∏ i, s i))).re).toNat)
      = Machine.binaryValue x * Machine.binaryValue y := by
  have hb := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n :=
    le_trans (by calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (d ^ 12) :=
                    Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))) hn
  exact main_step hs (by omega) (digits_fit hn2 hx hy _ hS2) hF' hFi' hF'ball
    (precision_ok_gen hd hn _ hS hεF hεI)

end Step

section Full

/-! ### Shrinking into the unit ball

The paper's numerical maps output fixed-point numbers of modulus at most one.
Radially shrinking a vector into the unit ball at most doubles its distance
to any point of the ball, so an approximation of a contraction can be made
to preserve the unit ball at the price of a factor two in the error. -/

/-- Radial shrinking of a vector into the closed unit ball. -/
noncomputable def shrinkBall {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  if ‖v‖ ≤ 1 then v else ((‖v‖⁻¹ : ℝ) : ℂ) • v

theorem norm_shrinkBall_le_one {ι : Type*} [Fintype ι] (v : ι → ℂ) : ‖shrinkBall v‖ ≤ 1 := by
  unfold shrinkBall
  split_ifs with h
  · exact h
  · push Not at h
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (by positivity)]

theorem norm_shrinkBall_sub_le {ι : Type*} [Fintype ι] (v w : ι → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖shrinkBall v - w‖ ≤ 2 * ‖v - w‖ := by
  unfold shrinkBall
  split_ifs with h
  · linarith [norm_nonneg (v - w)]
  · push Not at h
    have hv : 0 < ‖v‖ := by linarith
    have hr : ‖v‖ - 1 ≤ ‖v - w‖ := by
      have := norm_sub_norm_le v w
      linarith
    have hshrink : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ = ‖v‖ - 1 := by
      have : ((‖v‖⁻¹ : ℝ) : ℂ) • v - v = ((‖v‖⁻¹ - 1 : ℝ) : ℂ) • v := by
        push_cast; rw [sub_smul, one_smul]
      rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ h.le)]
      field_simp
      ring
    calc ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - w‖
        = ‖(((‖v‖⁻¹ : ℝ) : ℂ) • v - v) + (v - w)‖ := by congr 1; abel
      _ ≤ ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ + ‖v - w‖ := norm_add_le _ _
      _ = (‖v‖ - 1) + ‖v - w‖ := by rw [hshrink]
      _ ≤ 2 * ‖v - w‖ := by linarith

/-- Shrinking the outputs of an approximation of a contraction into the unit ball keeps it
an approximation, with twice the error. -/
theorem approxMap_shrink {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ℕ}
    {A' : (ι → ℂ) → (κ → ℂ)} {A : (ι → ℂ) →L[ℂ] (κ → ℂ)} {ε : ℝ} (hA : ‖A‖ ≤ 1)
    (h : ApproxMap p A' A ε) : ApproxMap p (fun v => shrinkBall (A' v)) A (2 * ε) := by
  intro v hv
  have hAv : ‖A v‖ ≤ 1 := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := ContinuousLinearMap.le_opNorm A v
      _ ≤ 1 * 1 := mul_le_mul hA hv (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc (2 : ℝ) ^ p * ‖shrinkBall (A' v) - A v‖
      ≤ 2 ^ p * (2 * ‖A' v - A v‖) :=
        mul_le_mul_of_nonneg_left (norm_shrinkBall_sub_le _ _ hAv) (by positivity)
    _ = 2 * (2 ^ p * ‖A' v - A v‖) := by ring
    _ ≤ 2 * ε := by linarith [h v hv]

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The ceiling of the square of a natural number cast to the reals. -/
theorem ceil_sq_natCast (a : ℕ) : ⌈((a : ℝ)) ^ 2⌉₊ = a ^ 2 := by
  rw [← Nat.cast_pow, Nat.ceil_natCast]

/-- The explicit factorization exponent at the paper's `α` is `γ + 2d`. -/
theorem factorization_exponent (d n : ℕ) :
    d * (2 * ⌈((alphaParam d n : ℕ) : ℝ) ^ 2⌉₊ + 2) = gammaParam d n + 2 * d := by
  rw [ceil_sq_natCast, gammaParam]; ring

/-- The numerical prime-grid transform shrunk into the unit ball. -/
noncomputable def mainTransformNum (γ : ℕ)
    (A' : (i : Fin d) → (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ))
    (B' : (i : Fin d) → (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ))
    (Ft' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ))
    (v : ((i : Fin d) → ZMod (s i)) → ℂ) : ((i : Fin d) → ZMod (s i)) → ℂ :=
  shrinkBall (((2 : ℂ) ^ γ) • tensorZR d t s B' (Ft' (tensorZR d s t A' v)))

/-- The recursive step given only an approximation of the power-of-two transform and the
per-coordinate numerical resampling maps, with the paper's parameters. -/
theorem main_step_full {n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hS : ∏ i, s i ≤ transformSize n) (hS2 : transformSize n < 2 * ∏ i, s i)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hθ : ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1))
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) = 1)
    (A' : (i : Fin d) → (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ))
    (B' : (i : Fin d) → (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ)) {εA εB εFt : ℝ}
    (hA' : ∀ i, ApproxMap (precision n) (A' i) (resampA (s i) (t i) (alphaParam d n : ℝ)) εA)
    (hB' : ∀ i, ApproxMap (precision n) (B' i)
      (resampB (s i) (t i) (alphaParam d n : ℝ) (hcop i) (J i)) εB)
    (hA'ball : ∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) (hB'ball : ∀ i v, ‖v‖ ≤ 1 → ‖B' i v‖ ≤ 1)
    (Ft' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ))
    (hFt : ApproxMap (precision n) Ft' (dftDCLM t) εFt)
    (hFt'ball : ∀ u, ‖u‖ ≤ 1 → ‖Ft' u‖ ≤ 1)
    (hεA : εA ≤ (precision n : ℝ) ^ 2) (hεB : εB ≤ (precision n : ℝ) ^ 2)
    (hεFt : εFt ≤ 8 * (transformSize n : ℝ) * (Nat.log 2 (transformSize n) : ℝ)) :
    evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
        approxConvS hs (precision n) (chunkSize n)
          (mainTransformNum (gammaParam d n + 2 * d) A' B' Ft')
          (fun v => negVec (mainTransformNum (gammaParam d n + 2 * d) A' B' Ft' v))
          (digitsOf (chunkSize n) x) (digitsOf (chunkSize n) y)
          (i.val : ZMod (∏ i, s i))).re).toNat)
      = Machine.binaryValue x * Machine.binaryValue y := by
  have hb := chunkSize_ge_4096 hd hn
  have hα : (1 : ℝ) ≤ ((alphaParam d n : ℕ) : ℝ) := by
    have := alphaParam_ge_two (d := d) (n := n) (by omega) (by omega)
    exact_mod_cast (by omega : 1 ≤ alphaParam d n)
  have hF := mainTransform_approx hst hcop hα hθ J hJ A' B' hA' hB' hA'ball hB'ball Ft' hFt
    hFt'ball
  rw [factorization_exponent] at hF
  have hF' := approxMap_shrink opNorm_dftDCLM_le hF
  have hFi := approxMap_negVec (p := precision n) hF'
  have hε := error_bound (γ := gammaParam d n + 2 * d) hεA hεB hεFt (d_p_sq_le hd hn)
  have hε' : 2 * (2 ^ (gammaParam d n + 2 * d) * (d * εB + εFt + d * εA)) ≤
      2 ^ (gammaParam d n + 2 * d + 5) * transformSize n * Nat.log 2 (transformSize n) := by
    rw [show gammaParam d n + 2 * d + 5 = (gammaParam d n + 2 * d + 4) + 1 by ring, pow_succ]
    linarith
  exact main_step_params hd hn hx hy hs hS hS2 hF' hFi
    (fun u hu => norm_shrinkBall_le_one _) hε' hε'

end Full

end IntegerMultBounds.NLogN
