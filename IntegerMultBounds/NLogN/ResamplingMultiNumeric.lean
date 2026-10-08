import IntegerMultBounds.NLogN.ResamplingMulti
import IntegerMultBounds.NLogN.ResamplingNumeric
import IntegerMultBounds.NLogN.TensorApproxV

/-! The numerical half of Theorem 4.1 of Harvey and van der Hoeven. Proved: the
coordinate-by-coordinate rectangular tensor of numerical maps on
`ZMod`-indexed arrays preserves the unit ball and accumulates the sum of the
per-coordinate scaled errors; its exact version, defined by the same
recursion, coincides with the matrix-defined tensor `tensorRCLM`; and for
coprime `s_i < t_i`, `α ≥ 1`, `α² θ_i ≥ 1`, with per-coordinate numerical
maps `Ã_i`, `B̃_i` approximating `A_i = S_i/2` and `B_i` with scaled errors
`εA`, `εB`, the tensors `⊗ Ã_i`, `⊗ B̃_i` approximate `⊗ A_i`, `⊗ B_i` with
scaled errors `d εA`, `d εB`, while `F_s = 2^(dγ) (⊗ B_i) F_t (⊗ A_i)`. The
per-coordinate approximations are hypotheses here; they are discharged for the
explicit numerical maps in `ResamplingNumeric.lean`. No cost is modeled. -/

open Real Complex

namespace IntegerMultBounds.NLogN

section RectZ

variable {d : ℕ}

instance mixFam_neZero {M N : Fin (d + 1) → ℕ} [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]
    (i : Fin (d + 1)) : NeZero (mixFam M N i) := by
  induction i using Fin.cases with
  | zero => exact inferInstanceAs (NeZero (M 0))
  | succ j => exact inferInstanceAs (NeZero (N j.succ))

/-- Apply `A : ZMod (M 0) → ZMod (N 0)` along coordinate `0`, lower coordinates at `N`. -/
def alongHeadZR {M N : Fin (d + 1) → ℕ} (A : (ZMod (M 0) → ℂ) → (ZMod (N 0) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ) :
    ((i : Fin (d + 1)) → ZMod (N i)) → ℂ :=
  fun k => A (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k))) (k 0)

/-- Apply the lower-dimensional rectangular map `B` on every coordinate-`0` slice. -/
def alongTailZR {M N : Fin (d + 1) → ℕ}
    (B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (M i)) → ℂ) :
    ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ :=
  fun k => B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)

/-- Coordinate-by-coordinate application of `d` rectangular numerical maps. -/
def tensorZR : (d : ℕ) → (M N : Fin d → ℕ) →
    ((i : Fin d) → (ZMod (M i) → ℂ) → (ZMod (N i) → ℂ)) →
    (((i : Fin d) → ZMod (M i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ)
  | 0, _, _, _ => fun u _ => u fun i => i.elim0
  | d + 1, M, N, A =>
    alongHeadZR (A 0) ∘ alongTailZR (tensorZR d (fun i => M i.succ) (fun i => N i.succ)
      fun i => A i.succ)

variable {M N : Fin (d + 1) → ℕ} [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]

theorem norm_headSliceZR_le (u : ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ)
    (t : (i : Fin d) → ZMod (N i.succ)) :
    ‖fun j₀ : ZMod (M 0) => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ t)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j₀
  exact norm_le_pi_norm u _

theorem norm_tailSliceZR_le (u : ((i : Fin (d + 1)) → ZMod (M i)) → ℂ) (j₀ : ZMod (M 0)) :
    ‖fun j' => u (Fin.cons j₀ j')‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j'
  exact norm_le_pi_norm u _

theorem norm_alongHeadZR_le {A : (ZMod (M 0) → ℂ) → (ZMod (N 0) → ℂ)}
    {u : ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ v, ‖v‖ ≤ ‖u‖ → ‖A v‖ ≤ C) : ‖alongHeadZR A u‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  intro k
  calc ‖alongHeadZR A u k‖
      = ‖A (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k))) (k 0)‖ :=
        rfl
    _ ≤ ‖A (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k)))‖ :=
        norm_le_pi_norm _ _
    _ ≤ C := hA _ (norm_headSliceZR_le u _)

theorem norm_alongTailZR_le
    {B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {u : ((i : Fin (d + 1)) → ZMod (M i)) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v, ‖v‖ ≤ ‖u‖ → ‖B v‖ ≤ C) : ‖alongTailZR B u‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  intro k
  calc ‖alongTailZR B u k‖ = ‖B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)‖ := rfl
    _ ≤ ‖B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
    _ ≤ C := hB _ (norm_tailSliceZR_le u _)

theorem alongHeadZR_ball {A : (ZMod (M 0) → ℂ) → (ZMod (N 0) → ℂ)}
    (hA : ∀ v, ‖v‖ ≤ 1 → ‖A v‖ ≤ 1) (u : ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ)
    (hu : ‖u‖ ≤ 1) : ‖alongHeadZR A u‖ ≤ 1 :=
  norm_alongHeadZR_le zero_le_one fun v hv => hA v (le_trans hv hu)

theorem alongTailZR_ball
    {B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    (hB : ∀ v, ‖v‖ ≤ 1 → ‖B v‖ ≤ 1) (u : ((i : Fin (d + 1)) → ZMod (M i)) → ℂ)
    (hu : ‖u‖ ≤ 1) : ‖alongTailZR B u‖ ≤ 1 :=
  norm_alongTailZR_le zero_le_one fun v hv => hB v (le_trans hv hu)

/-- Restriction to a coordinate-`0` line, as a continuous linear map. -/
noncomputable def headSliceZRCLM (t : (i : Fin d) → ZMod (N i.succ)) :
    (((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ) →L[ℂ] (ZMod (M 0) → ℂ) :=
  ContinuousLinearMap.pi fun j₀ =>
    ContinuousLinearMap.proj (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ t)

/-- Restriction to a coordinate-`0` slice, as a continuous linear map. -/
noncomputable def tailSliceZRCLM (j₀ : ZMod (M 0)) :
    (((i : Fin (d + 1)) → ZMod (M i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (M i.succ)) → ℂ) :=
  ContinuousLinearMap.pi fun j' => ContinuousLinearMap.proj (Fin.cons j₀ j')

/-- The continuous linear rectangular action along coordinate `0`. -/
noncomputable def alongHeadZRCLM (A : (ZMod (M 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ)) :
    (((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ) →L[ℂ]
      (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (k 0)).comp (A.comp (headSliceZRCLM (Fin.tail k)))

/-- The continuous linear slice-wise action of a lower-dimensional rectangular map. -/
noncomputable def alongTailZRCLM
    (B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ)) :
    (((i : Fin (d + 1)) → ZMod (M i)) → ℂ) →L[ℂ]
      (((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (Fin.tail k)).comp (B.comp (tailSliceZRCLM (k 0)))

omit [∀ i, NeZero (M i)] [∀ i, NeZero (N i)] in
theorem alongHeadZRCLM_apply (A : (ZMod (M 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (mixFam M N i)) → ℂ) :
    alongHeadZRCLM A u = alongHeadZR A u := by
  funext k
  simp [alongHeadZRCLM, headSliceZRCLM, alongHeadZR]

omit [∀ i, NeZero (M i)] [∀ i, NeZero (N i)] in
theorem alongTailZRCLM_apply
    (B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (M i)) → ℂ) : alongTailZRCLM B u = alongTailZR B u := by
  funext k
  rfl

theorem opNorm_alongHeadZRCLM_le (A : (ZMod (M 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ))
    (hA : ‖A‖ ≤ 1) : ‖alongHeadZRCLM (d := d) (M := M) (N := N) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongHeadZRCLM_apply, one_mul]
  apply norm_alongHeadZR_le (norm_nonneg _)
  intro v hv
  calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem opNorm_alongTailZRCLM_le
    (B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (hB : ‖B‖ ≤ 1) : ‖alongTailZRCLM (M := M) (N := N) B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongTailZRCLM_apply, one_mul]
  apply norm_alongTailZR_le (norm_nonneg _)
  intro v hv
  calc ‖B v‖ ≤ ‖B‖ * ‖v‖ := B.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem approxMap_alongHeadZR {p : ℕ} {A' : (ZMod (M 0) → ℂ) → (ZMod (N 0) → ℂ)}
    {A : (ZMod (M 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ)} {ε : ℝ} (h : ApproxMap p A' A ε) :
    ApproxMap p (alongHeadZR (d := d) A') (alongHeadZRCLM A) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongHeadZRCLM_apply]
  have : ‖alongHeadZR A' u - alongHeadZR A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k)))
      (le_trans (norm_headSliceZR_le u _) hu)
    calc ‖(alongHeadZR A' u - alongHeadZR A u) k‖
        = ‖(A' (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k))))
            (k 0)‖ := rfl
      _ ≤ ‖A' (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons (α := fun i => ZMod (mixFam M N i)) j₀ (Fin.tail k)))‖ :=
          norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongHeadZR A' u - alongHeadZR A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

theorem approxMap_alongTailZR {p : ℕ}
    {B' : (((i : Fin d) → ZMod (M i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {B : (((i : Fin d) → ZMod (M i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {ε : ℝ} (h : ApproxMap p B' B ε) :
    ApproxMap p (alongTailZR (M := M) (N := N) B') (alongTailZRCLM B) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongTailZRCLM_apply]
  have : ‖alongTailZR B' u - alongTailZR B u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j' => u (Fin.cons (k 0) j')) (le_trans (norm_tailSliceZR_le u _) hu)
    calc ‖(alongTailZR B' u - alongTailZR B u) k‖
        = ‖(B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))) (Fin.tail k)‖ := rfl
      _ ≤ ‖B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongTailZR B' u - alongTailZR B u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

end RectZ

section TensorZR

/-- The exact tensor product of `d` rectangular continuous linear maps, by the same
coordinate-by-coordinate recursion as `tensorZR`. -/
noncomputable def tensorZRCLM : (d : ℕ) → (M N : Fin d → ℕ) → [∀ i, NeZero (M i)] →
    [∀ i, NeZero (N i)] → ((i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) →
    (((i : Fin d) → ZMod (M i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i)) → ℂ)
  | 0, _, _, _, _, _ => ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj fun i => i.elim0
  | d + 1, M, N, _, _, A =>
    alongHeadZRCLM (A 0) ∘L
      alongTailZRCLM (tensorZRCLM d (fun i => M i.succ) (fun i => N i.succ) fun i => A i.succ)

theorem tensorZRCLM_apply : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]
    (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (u : ((i : Fin d) → ZMod (M i)) → ℂ),
    tensorZRCLM d M N A u = tensorZR d M N (fun i => (A i : (ZMod (M i) → ℂ) → _)) u
  | 0, _, _, _, _, _, _ => by
    funext k
    simp [tensorZRCLM, tensorZR]
  | d + 1, M, N, _, _, A, u => by
    simp only [tensorZRCLM, tensorZR, ContinuousLinearMap.comp_apply, Function.comp_apply,
      alongHeadZRCLM_apply, alongTailZRCLM_apply]
    congr 1
    funext k
    exact congrFun (tensorZRCLM_apply d _ _ _ _) _

theorem tensorZR_ball : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]
    (A' : (i : Fin d) → (ZMod (M i) → ℂ) → (ZMod (N i) → ℂ)),
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ∀ u : ((i : Fin d) → ZMod (M i)) → ℂ, ‖u‖ ≤ 1 → ‖tensorZR d M N A' u‖ ≤ 1
  | 0, _, _, _, _, _, _, u, hu => by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    exact le_trans (norm_le_pi_norm u _) hu
  | d + 1, M, N, _, _, A', hA', u, hu =>
    alongHeadZR_ball (hA' 0) _
      (alongTailZR_ball (tensorZR_ball d _ _ _ fun i => hA' i.succ) u hu)

theorem opNorm_tensorZRCLM_le : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)]
    [∀ i, NeZero (N i)] (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)),
    (∀ i, ‖A i‖ ≤ 1) → ‖tensorZRCLM d M N A‖ ≤ 1
  | 0, _, _, _, _, A, _ => by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    simp only [tensorZRCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm u _
  | d + 1, M, N, _, _, A, hA => by
    simp only [tensorZRCLM]
    calc ‖alongHeadZRCLM (A 0) ∘L
          alongTailZRCLM (tensorZRCLM d (fun i => M i.succ) (fun i => N i.succ) fun i => A i.succ)‖
        ≤ ‖alongHeadZRCLM (A 0)‖ *
          ‖alongTailZRCLM (tensorZRCLM d (fun i => M i.succ) (fun i => N i.succ)
            fun i => A i.succ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact opNorm_alongHeadZRCLM_le _ (hA 0)
          · exact opNorm_alongTailZRCLM_le _ (opNorm_tensorZRCLM_le d _ _ _ fun i => hA i.succ)
      _ = 1 := one_mul _

/-- Lemma 2.11 for rectangular numerical maps on `ZMod`-indexed arrays. -/
theorem approxMap_tensorZR {p : ℕ} : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)]
    [∀ i, NeZero (N i)] (A' : (i : Fin d) → (ZMod (M i) → ℂ) → (ZMod (N i) → ℂ))
    (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) (ε : Fin d → ℝ),
    (∀ i, ‖A i‖ ≤ 1) → (∀ i, ApproxMap p (A' i) (A i) (ε i)) →
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ApproxMap p (tensorZR d M N A') (tensorZRCLM d M N A) (∑ i, ε i)
  | 0, _, _, _, _, _, _, _, _, _, _ => by
    intro u _
    simp [tensorZR, tensorZRCLM]
  | d + 1, M, N, _, _, A', A, ε, hA, h, hball => by
    rw [Fin.sum_univ_succ]
    exact approx_comp (opNorm_alongHeadZRCLM_le _ (hA 0))
      (approxMap_alongTailZR (approxMap_tensorZR d _ _ _ _ _ (fun i => hA i.succ)
        (fun i => h i.succ) (fun i => hball i.succ)))
      (approxMap_alongHeadZR (h 0))
      (fun u hu => alongTailZR_ball (tensorZR_ball d _ _ _ fun i => hball i.succ) u hu)

/-- The recursive exact tensor expands into the matrix entries of the factors. -/
theorem tensorZR_clm_apply : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]
    (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (u : ((i : Fin d) → ZMod (M i)) → ℂ) (k : (i : Fin d) → ZMod (N i)),
    tensorZR d M N (fun i => (A i : (ZMod (M i) → ℂ) → _)) u k =
      ∑ j, (∏ i, matOf (A i) (k i) (j i)) * u j
  | 0, _, _, _, _, _, u, k => by
    simp only [tensorZR, Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty,
      Finset.prod_empty, one_mul]
    congr
  | d + 1, M, N, _, _, A, u, k => by
    show (A 0) (fun j₀ => tensorZR d _ _ _ (fun j' => u (Fin.cons j₀ j')) (Fin.tail k)) (k 0) = _
    rw [clm_apply_eq_sum]
    simp_rw [tensorZR_clm_apply d _ _ _ _ _]
    rw [← Equiv.sum_comp (Fin.consEquiv fun i => ZMod (M i)), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Finset.mul_sum, Fin.tail]
    refine Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j' _ => ?_
    ring

/-- The recursive and the matrix-defined exact tensors agree. -/
theorem tensorZRCLM_eq_tensorRCLM {d : ℕ} {M N : Fin d → ℕ} [∀ i, NeZero (M i)]
    [∀ i, NeZero (N i)] (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) :
    tensorZRCLM d M N A = tensorRCLM A := by
  ext u k
  rw [tensorZRCLM_apply, tensorZR_clm_apply, tensorRCLM_apply]

end TensorZR

section Numeric

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ} {p : ℕ}

/-- Theorem 4.1, numerical half: the tensors of per-coordinate numerical maps approximate
the tensors of `A_i` and `B_i` with `d` times the per-coordinate error, while the exact
tensors factor the source transform through the target transform. -/
theorem resampling_multi_numeric (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1))
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) α) = 1)
    (A' : (i : Fin d) → (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ))
    (B' : (i : Fin d) → (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ)) {εA εB : ℝ}
    (hA' : ∀ i, ApproxMap p (A' i) (resampA (s i) (t i) α) εA)
    (hB' : ∀ i, ApproxMap p (B' i) (resampB (s i) (t i) α (hcop i) (J i)) εB)
    (hA'ball : ∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) (hB'ball : ∀ i v, ‖v‖ ≤ 1 → ‖B' i v‖ ≤ 1) :
    dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
        (tensorRCLM (fun i => resampB (s i) (t i) α (hcop i) (J i)) ∘L dftDCLM t ∘L
          tensorRCLM (fun i => resampA (s i) (t i) α)) ∧
      ApproxMap p (tensorZR d s t A') (tensorRCLM (fun i => resampA (s i) (t i) α)) (d * εA) ∧
      ApproxMap p (tensorZR d t s B')
        (tensorRCLM (fun i => resampB (s i) (t i) α (hcop i) (J i))) (d * εB) := by
  have h := fun i => resampling_factorization_explicit (hst i) (hcop i) hα (hθ i) (J i) (hJ i)
  refine ⟨?_, ?_, ?_⟩
  · rw [dftDCLM_eq_tensor, dftDCLM_eq_tensor]
    have e : (fun i => dftCLM (s i)) = fun i => ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB (s i) (t i) α (hcop i) (J i) ∘L dftCLM (t i) ∘L resampA (s i) (t i) α) :=
      funext fun i => (h i).1
    rw [e, tensorRCLM_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
      mul_comm (2 * ⌈α ^ 2⌉₊ + 2) d,
      tensorRCLM_comp (fun i => resampB (s i) (t i) α (hcop i) (J i))
        (fun i => dftCLM (t i) ∘L resampA (s i) (t i) α),
      tensorRCLM_comp (fun i => dftCLM (t i)) (fun i => resampA (s i) (t i) α)]
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d s t A' (fun i => resampA (s i) (t i) α) (fun _ => εA)
      (fun i => (h i).2.1) hA' hA'ball
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d t s B' (fun i => resampB (s i) (t i) α (hcop i) (J i))
      (fun _ => εB) (fun i => (h i).2.2) hB' hB'ball
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

end Numeric

end IntegerMultBounds.NLogN
