import IntegerMultBounds.NLogN.NeumannHalved

/-! Lemma 7.1 with the manuscript's numerical maps: no clamps. For `α ≥ 2`,
`‖A‖ ≤ 3/4`, so the unclamped window sums `Ã` land in the unit disk once their
scaled error is below `2^p/4`; with the clamp-free `B̃₀ = D̃' J̃' C` of
`NeumannHalved` (window `⌊√p⌋ + 1`) both maps approximate `A`, `B₀` with errors
below `p²` and are contractions on the unit disk. These are the maps the tape
machines compute. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

theorem four_sq_le_pow (p : ℕ) (hp : 13 ≤ p) : 4 * p ^ 2 ≤ 2 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    have : 4 * (n + 1) ^ 2 ≤ 2 * (4 * n ^ 2) := by nlinarith
    omega

/-- `‖A‖ ≤ 3/4` for `α ≥ 2`. -/
theorem opNorm_resampA_le_three_quarters (hα : 2 ≤ α) : ‖resampA s t α‖ ≤ 3 / 4 := by
  have h := opNorm_resampSCLM_le (s := s) (t := t) (by linarith : (0 : ℝ) < α)
  have h1 : 1 / α ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hα
  rw [resampA, norm_smul, norm_inv, RCLike.norm_two]
  nlinarith [norm_nonneg (resampSCLM s t α)]

/-- An approximation of a map of norm at most `3/4` with scaled error at most
`2^p/4` stays in the unit disk. -/
theorem ball_of_approx {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {ε : ℝ}
    (hA : ‖A‖ ≤ 3 / 4) (h : ApproxMap p A' A ε) (hε : 4 * ε ≤ 2 ^ p) (v : V) (hv : ‖v‖ ≤ 1) :
    ‖A' v‖ ≤ 1 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 : ‖A' v - A v‖ ≤ ε / 2 ^ p := by rw [le_div_iff₀ hp, mul_comm]; exact h v hv
  have h2 : ‖A v‖ ≤ 3 / 4 := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := le_opNorm _ _
      _ ≤ 3 / 4 * 1 := by gcongr
      _ = 3 / 4 := mul_one _
  have h3 : ε / 2 ^ p ≤ 1 / 4 := by rw [div_le_iff₀ hp]; linarith
  calc ‖A' v‖ = ‖(A' v - A v) + A v‖ := by rw [sub_add_cancel]
    _ ≤ ‖A' v - A v‖ + ‖A v‖ := norm_add_le _ _
    _ ≤ 1 := by linarith

/-- Lemma 7.1 with the manuscript's unclamped numerical maps, one dimension. -/
theorem permuted_numeric_manuscript (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ s t α J ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB₀ s t α J‖ ≤ 1 ∧
      ApproxMap p (resampANum s t m (resampTermNum p s t α)) (resampA s t α) (errA m) ∧
      ApproxMap p (resampB₀NumH p (sqrtWindow p) s t α) (resampB₀ s t α J)
        (errB₀H (sqrtWindow p)) ∧
      errA m < (p : ℝ) ^ 2 ∧ errB₀H (sqrtWindow p) < (p : ℝ) ^ 2 ∧
      (∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ‖resampANum s t m (resampTermNum p s t α) u‖ ≤ 1) ∧
      (∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀NumH p (sqrtWindow p) s t α w‖ ≤ 1) := by
  obtain ⟨J, hJ, hJ', hJn⟩ := exists_left_inverse hst (by linarith : (0 : ℝ) < α) hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop (by linarith) hθ J hJ
  have hAx := approxMap_resampANum_explicit (s := s) (t := t) (by linarith) hαp hm hm1
  have hεA : errA m < (p : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  have hpow : (4 : ℝ) * (p : ℝ) ^ 2 ≤ 2 ^ p := by exact_mod_cast four_sq_le_pow p hp
  have hα0 : (0 : ℝ) < α := by linarith
  have hBx := approxMap_resampB₀NumH_sqrt hst hα0 hθ hp hJ'
  have h4 : 4 * errA m ≤ 2 ^ p := by linarith
  have hA34 := opNorm_resampA_le_three_quarters (s := s) (t := t) hα
  have hAb : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ‖resampANum s t m (resampTermNum p s t α) u‖ ≤ 1 :=
    fun u hu => ball_of_approx hA34 hAx h4 u hu
  have hBb : ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀NumH p (sqrtWindow p) s t α w‖ ≤ 1 :=
    fun w hw => resampB₀NumH_sqrt_ball hst hα0 hθ hp hJ' w hw
  refine ⟨J, ?_, hA, opNorm_resampB₀_le J hJn, hAx, hBx, hεA, errB₀H_sqrt_lt_sq hp, hAb, hBb⟩
  rw [resampB_eq hcop J] at heq
  rw [← permSEquiv_coe hcop, heq]
  ext u j
  simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end IntegerMultBounds.NLogN
