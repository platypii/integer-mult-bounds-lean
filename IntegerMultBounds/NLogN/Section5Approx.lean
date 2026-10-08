import IntegerMultBounds.NLogN.FixedOps
import IntegerMultBounds.NLogN.Neumann

/-! The error bookkeeping of Propositions 5.2 and 5.3 of Harvey and van der
Hoeven, stated abstractly over normed spaces with the paper's conventions:
exact maps are contractions, approximations keep the unit ball, and errors are
scaled by `2^p`. Proved: a three-fold composition of approximations adds the
three errors; scaling an approximation by a natural number `c` scales its
error by `c` (no re-rounding term appears, because a scaled fixed-point output
is already fixed-point and `rhoC` fixes it, see `rhoC_of_isFixed`); hence the
scaled transform `2^γ B F A` is approximated with error `2^γ (ε_B + ε_F + ε_A)`;
the forward, rounded pointwise, inverse pipeline approximates the exact
convolution map with error `ε_I + 2 ε_F + 2`, and `S` times that after scaling
by `S`. The maps and their errors are hypotheses, not constructions, and no
cost model is attached. -/

namespace IntegerMultBounds.NLogN

section Linear

variable {U V W X : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Three-fold composition of approximations adds their errors. -/
theorem approx_comp₃ {p : ℕ} {A' : U → V} {A : U →L[ℂ] V} {F' : V → W} {F : V →L[ℂ] W}
    {B' : W → X} {B : W →L[ℂ] X} {εA εF εB : ℝ}
    (hB : ‖B‖ ≤ 1) (hF : ‖F‖ ≤ 1)
    (hA' : ApproxMap p A' A εA) (hF' : ApproxMap p F' F εF) (hB' : ApproxMap p B' B εB)
    (hA'ball : ∀ u, ‖u‖ ≤ 1 → ‖A' u‖ ≤ 1) (hF'ball : ∀ v, ‖v‖ ≤ 1 → ‖F' v‖ ≤ 1) :
    ApproxMap p (B' ∘ F' ∘ A') (B ∘L F ∘L A) (εB + εF + εA) := by
  have h1 : ApproxMap p (F' ∘ A') (F ∘L A) (εF + εA) := approx_comp hF hA' hF' hA'ball
  have hball : ∀ u, ‖u‖ ≤ 1 → ‖(F' ∘ A') u‖ ≤ 1 := fun u hu => hF'ball _ (hA'ball u hu)
  have h2 := approx_comp hB h1 hB' hball
  rw [← add_assoc] at h2
  exact h2

/-- Scaling an approximation by a natural number scales its error. -/
theorem approxMap_smul_nat {p : ℕ} {G' : V → W} {G : V →L[ℂ] W} {ε : ℝ} (c : ℕ)
    (h : ApproxMap p G' G ε) :
    ApproxMap p (fun v => (c : ℂ) • G' v) ((c : ℂ) • G) (c * ε) := by
  intro v hv
  have hc : ‖(c : ℂ)‖ = c := by simp
  have := h v hv
  simp only [smul_apply]
  rw [← smul_sub, norm_smul, hc]
  calc (2 : ℝ) ^ p * (c * ‖G' v - G v‖) = c * (2 ^ p * ‖G' v - G v‖) := by ring
    _ ≤ c * ε := by gcongr

/-- Proposition 5.2: the scaled factorisation `F_s = 2^γ B F A` is approximated by
`2^γ B' F' A'` with error `2^γ (ε_B + ε_F + ε_A)`. -/
theorem prop52 {p γ : ℕ} {A' : U → V} {A : U →L[ℂ] V} {F' : V → W} {F : V →L[ℂ] W}
    {B' : W → U} {B : W →L[ℂ] U} {Fs : U →L[ℂ] U} {εA εF εB : ℝ}
    (hB : ‖B‖ ≤ 1) (hF : ‖F‖ ≤ 1)
    (hA' : ApproxMap p A' A εA) (hF' : ApproxMap p F' F εF) (hB' : ApproxMap p B' B εB)
    (hA'ball : ∀ u, ‖u‖ ≤ 1 → ‖A' u‖ ≤ 1) (hF'ball : ∀ v, ‖v‖ ≤ 1 → ‖F' v‖ ≤ 1)
    (hFs : Fs = ((2 : ℂ) ^ γ) • (B ∘L F ∘L A)) :
    ApproxMap p (fun v => ((2 : ℂ) ^ γ) • B' (F' (A' v))) Fs
      (2 ^ γ * (εB + εF + εA)) := by
  subst hFs
  have h := approxMap_smul_nat (2 ^ γ) (approx_comp₃ hB hF hA' hF' hB' hA'ball hF'ball)
  have e1 : ((2 ^ γ : ℕ) : ℂ) = (2 : ℂ) ^ γ := by push_cast; rfl
  have e2 : ((2 ^ γ : ℕ) : ℝ) = (2 : ℝ) ^ γ := by push_cast; rfl
  simp only [e1, e2] at h
  exact h

end Linear

section Convolution

variable {ι : Type*} [Fintype ι]

/-- Pointwise product of vectors. -/
def pw (x y : ι → ℂ) : ι → ℂ := fun j => x j * y j

/-- The convolution pipeline: approximate forward transforms, rounded pointwise products,
approximate inverse transform. -/
noncomputable def convVia (p : ℕ) (F' Fi' : (ι → ℂ) → (ι → ℂ)) (u v : ι → ℂ) : ι → ℂ :=
  Fi' (fun j => rhoC p (F' u j * F' v j))

/-- Proposition 5.3: the pipeline approximates `F_i (F u · F v)` with error
`ε_I + 2 ε_F + 2` on unit-ball inputs. -/
theorem prop53_err {p : ℕ} {F' Fi' : (ι → ℂ) → (ι → ℂ)} {F Fi : (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {εF εI : ℝ} (hF : ‖F‖ ≤ 1) (hFi : ‖Fi‖ ≤ 1)
    (hF' : ApproxMap p F' F εF) (hFi' : ApproxMap p Fi' Fi εI)
    (hF'ball : ∀ u, ‖u‖ ≤ 1 → ‖F' u‖ ≤ 1) {u v : ι → ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    2 ^ p * ‖convVia p F' Fi' u v - Fi (pw (F u) (F v))‖ ≤ εI + (2 * εF + 2) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεF : 0 ≤ εF := le_trans (by positivity) (hF' u hu)
  set z' : ι → ℂ := fun j => rhoC p (F' u j * F' v j) with hz'
  have hball : ∀ w, ‖w‖ ≤ 1 → ∀ j, ‖F' w j‖ ≤ 1 := fun w hw j =>
    (norm_le_pi_norm (F' w) j).trans (hF'ball w hw)
  have hFball : ∀ w, ‖w‖ ≤ 1 → ∀ j, ‖F w j‖ ≤ 1 := by
    intro w hw j
    refine (norm_le_pi_norm (F w) j).trans ?_
    calc ‖F w‖ ≤ ‖F‖ * ‖w‖ := F.le_opNorm w
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  have hz'ball : ‖z'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    calc ‖z' j‖ ≤ ‖F' u j * F' v j‖ := norm_rhoC_le _ _
      _ = ‖F' u j‖ * ‖F' v j‖ := norm_mul _ _
      _ ≤ 1 * 1 := by gcongr; exacts [hball u hu j, hball v hv j]
      _ = 1 := one_mul _
  have hcoord : ∀ w, ‖w‖ ≤ 1 → ∀ j, 2 ^ p * ‖F' w j - F w j‖ ≤ εF := by
    intro w hw j
    have h1 := hF' w hw
    have h2 : ‖F' w j - F w j‖ ≤ ‖F' w - F w‖ := by
      have := norm_le_pi_norm (F' w - F w) j
      simpa using this
    calc 2 ^ p * ‖F' w j - F w j‖ ≤ 2 ^ p * ‖F' w - F w‖ := by gcongr
      _ ≤ εF := h1
  have hz : ∀ j, 2 ^ p * ‖z' j - F u j * F v j‖ ≤ 2 + εF + εF := fun j =>
    approx_mul_round (hball u hu j) (hball v hv j) (hFball u hu j)
      (hcoord u hu j) (hcoord v hv j)
  have hzvec : 2 ^ p * ‖z' - pw (F u) (F v)‖ ≤ 2 * εF + 2 := by
    have hnn : (0 : ℝ) ≤ (2 * εF + 2) / 2 ^ p := by positivity
    have h : ‖z' - pw (F u) (F v)‖ ≤ (2 * εF + 2) / 2 ^ p := by
      rw [pi_norm_le_iff_of_nonneg hnn]
      intro j
      rw [le_div_iff₀ hp, mul_comm]
      have := hz j
      simp only [Pi.sub_apply, pw]
      linarith
    calc 2 ^ p * ‖z' - pw (F u) (F v)‖ ≤ 2 ^ p * ((2 * εF + 2) / 2 ^ p) := by gcongr
      _ = 2 * εF + 2 := by field_simp
  show 2 ^ p * ‖Fi' z' - Fi (pw (F u) (F v))‖ ≤ εI + (2 * εF + 2)
  exact approx_apply (A' := Fi') hFi hFi' hz'ball hzvec

/-- Proposition 5.3 after scaling by `S`. -/
theorem prop53_scaled {p : ℕ} {F' Fi' : (ι → ℂ) → (ι → ℂ)} {F Fi : (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {εF εI : ℝ} (S : ℕ) (hF : ‖F‖ ≤ 1) (hFi : ‖Fi‖ ≤ 1)
    (hF' : ApproxMap p F' F εF) (hFi' : ApproxMap p Fi' Fi εI)
    (hF'ball : ∀ u, ‖u‖ ≤ 1 → ‖F' u‖ ≤ 1) {u v : ι → ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    2 ^ p * ‖(S : ℂ) • convVia p F' Fi' u v - (S : ℂ) • Fi (pw (F u) (F v))‖
      ≤ S * (εI + (2 * εF + 2)) := by
  have hS : ‖(S : ℂ)‖ = S := by simp
  rw [← smul_sub, norm_smul, hS]
  calc (2 : ℝ) ^ p * (S * ‖convVia p F' Fi' u v - Fi (pw (F u) (F v))‖)
      = S * (2 ^ p * ‖convVia p F' Fi' u v - Fi (pw (F u) (F v))‖) := by ring
    _ ≤ S * (εI + (2 * εF + 2)) := by
        gcongr
        exact prop53_err hF hFi hF' hFi' hF'ball hu hv

end Convolution

end IntegerMultBounds.NLogN
