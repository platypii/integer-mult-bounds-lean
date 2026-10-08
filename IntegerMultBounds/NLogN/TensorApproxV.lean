import IntegerMultBounds.NLogN.TensorApproxD

/-! Lemma 2.11 of Harvey and van der Hoeven for arrays with values in an
arbitrary normed complex space, indexed by `(i : Fin d) → Fin (N i)`; this is
the form needed over the synthetic ring, viewed as `Fin r → ℂ`. Proved: applying
a map along coordinate `0`, or a lower-dimensional map on every coordinate-`0`
slice, keeps norms and approximation errors; the coordinate-by-coordinate
tensor of approximations approximates the tensor of the exact maps with the
sum of the errors; and, for rectangular maps between different lengths, the
tensor of compositions is the composition of tensors. No cost model is
attached. -/

open Complex

namespace IntegerMultBounds.NLogN

variable {V : Type*} [NormedAddCommGroup V]

section AlongV

variable {d : ℕ} {N : Fin (d + 1) → ℕ}

/-- Apply `A` along coordinate `0` of a `d + 1`-dimensional `V`-valued array. -/
def alongHeadV (A : (Fin (N 0) → V) → (Fin (N 0) → V))
    (u : ((i : Fin (d + 1)) → Fin (N i)) → V) : ((i : Fin (d + 1)) → Fin (N i)) → V :=
  fun k => A (fun j₀ => u (Fin.cons j₀ (Fin.tail k))) (k 0)

/-- Apply the lower-dimensional map `B` on every coordinate-`0` slice. -/
def alongTailV (B : (((i : Fin d) → Fin (N i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V))
    (u : ((i : Fin (d + 1)) → Fin (N i)) → V) : ((i : Fin (d + 1)) → Fin (N i)) → V :=
  fun k => B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)

theorem norm_headSliceV_le (u : ((i : Fin (d + 1)) → Fin (N i)) → V)
    (t : (i : Fin d) → Fin (N i.succ)) :
    ‖fun j₀ => u (Fin.cons j₀ t)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j₀
  exact norm_le_pi_norm u _

theorem norm_tailSliceV_le (u : ((i : Fin (d + 1)) → Fin (N i)) → V) (j₀ : Fin (N 0)) :
    ‖fun j' => u (Fin.cons j₀ j')‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j'
  exact norm_le_pi_norm u _

theorem norm_alongHeadV_le {A : (Fin (N 0) → V) → (Fin (N 0) → V)}
    {u : ((i : Fin (d + 1)) → Fin (N i)) → V} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ v, ‖v‖ ≤ ‖u‖ → ‖A v‖ ≤ M) : ‖alongHeadV A u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro k
  calc ‖alongHeadV A u k‖ = ‖A (fun j₀ => u (Fin.cons j₀ (Fin.tail k))) (k 0)‖ := rfl
    _ ≤ ‖A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))‖ := norm_le_pi_norm _ _
    _ ≤ M := hA _ (norm_headSliceV_le u _)

theorem norm_alongTailV_le
    {B : (((i : Fin d) → Fin (N i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    {u : ((i : Fin (d + 1)) → Fin (N i)) → V} {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ v, ‖v‖ ≤ ‖u‖ → ‖B v‖ ≤ M) : ‖alongTailV B u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro k
  calc ‖alongTailV B u k‖ = ‖B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)‖ := rfl
    _ ≤ ‖B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
    _ ≤ M := hB _ (norm_tailSliceV_le u _)

theorem alongHeadV_ball {A : (Fin (N 0) → V) → (Fin (N 0) → V)}
    (hA : ∀ v, ‖v‖ ≤ 1 → ‖A v‖ ≤ 1) (u : ((i : Fin (d + 1)) → Fin (N i)) → V)
    (hu : ‖u‖ ≤ 1) : ‖alongHeadV A u‖ ≤ 1 :=
  norm_alongHeadV_le zero_le_one fun v hv => hA v (le_trans hv hu)

theorem alongTailV_ball
    {B : (((i : Fin d) → Fin (N i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    (hB : ∀ v, ‖v‖ ≤ 1 → ‖B v‖ ≤ 1) (u : ((i : Fin (d + 1)) → Fin (N i)) → V)
    (hu : ‖u‖ ≤ 1) : ‖alongTailV B u‖ ≤ 1 :=
  norm_alongTailV_le zero_le_one fun v hv => hB v (le_trans hv hu)

variable [NormedSpace ℂ V]

/-- Restriction to a coordinate-`0` line, as a continuous linear map. -/
noncomputable def headSliceVCLM (t : (i : Fin d) → Fin (N i.succ)) :
    (((i : Fin (d + 1)) → Fin (N i)) → V) →L[ℂ] (Fin (N 0) → V) :=
  ContinuousLinearMap.pi fun j₀ => ContinuousLinearMap.proj (Fin.cons j₀ t)

/-- Restriction to a coordinate-`0` slice, as a continuous linear map. -/
noncomputable def tailSliceVCLM (j₀ : Fin (N 0)) :
    (((i : Fin (d + 1)) → Fin (N i)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V) :=
  ContinuousLinearMap.pi fun j' => ContinuousLinearMap.proj (Fin.cons j₀ j')

/-- The continuous linear action along coordinate `0`. -/
noncomputable def alongHeadVCLM (A : (Fin (N 0) → V) →L[ℂ] (Fin (N 0) → V)) :
    (((i : Fin (d + 1)) → Fin (N i)) → V) →L[ℂ] (((i : Fin (d + 1)) → Fin (N i)) → V) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (k 0)).comp (A.comp (headSliceVCLM (Fin.tail k)))

/-- The continuous linear slice-wise action of a lower-dimensional map. -/
noncomputable def alongTailVCLM
    (B : (((i : Fin d) → Fin (N i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V)) :
    (((i : Fin (d + 1)) → Fin (N i)) → V) →L[ℂ] (((i : Fin (d + 1)) → Fin (N i)) → V) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (Fin.tail k)).comp (B.comp (tailSliceVCLM (k 0)))

theorem alongHeadVCLM_apply (A : (Fin (N 0) → V) →L[ℂ] (Fin (N 0) → V))
    (u : ((i : Fin (d + 1)) → Fin (N i)) → V) : alongHeadVCLM A u = alongHeadV A u := by
  funext k
  simp [alongHeadVCLM, headSliceVCLM, alongHeadV]

theorem alongTailVCLM_apply
    (B : (((i : Fin d) → Fin (N i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V))
    (u : ((i : Fin (d + 1)) → Fin (N i)) → V) : alongTailVCLM B u = alongTailV B u := by
  funext k
  simp [alongTailVCLM, tailSliceVCLM, alongTailV]

theorem opNorm_alongHeadVCLM_le (A : (Fin (N 0) → V) →L[ℂ] (Fin (N 0) → V))
    (hA : ‖A‖ ≤ 1) : ‖alongHeadVCLM (d := d) (N := N) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongHeadVCLM_apply, one_mul]
  apply norm_alongHeadV_le (norm_nonneg _)
  intro v hv
  calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem opNorm_alongTailVCLM_le
    (B : (((i : Fin d) → Fin (N i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V))
    (hB : ‖B‖ ≤ 1) : ‖alongTailVCLM (N := N) B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongTailVCLM_apply, one_mul]
  apply norm_alongTailV_le (norm_nonneg _)
  intro v hv
  calc ‖B v‖ ≤ ‖B‖ * ‖v‖ := B.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem approxMap_alongHeadV {p : ℕ} {A' : (Fin (N 0) → V) → (Fin (N 0) → V)}
    {A : (Fin (N 0) → V) →L[ℂ] (Fin (N 0) → V)} {ε : ℝ} (h : ApproxMap p A' A ε) :
    ApproxMap p (alongHeadV (d := d) A') (alongHeadVCLM A) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongHeadVCLM_apply]
  have : ‖alongHeadV A' u - alongHeadV A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
      (le_trans (norm_headSliceV_le u _) hu)
    calc ‖(alongHeadV A' u - alongHeadV A u) k‖
        = ‖(A' (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))) (k 0)‖ := rfl
      _ ≤ ‖A' (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongHeadV A' u - alongHeadV A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

theorem approxMap_alongTailV {p : ℕ}
    {B' : (((i : Fin d) → Fin (N i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    {B : (((i : Fin d) → Fin (N i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V)}
    {ε : ℝ} (h : ApproxMap p B' B ε) :
    ApproxMap p (alongTailV (N := N) B') (alongTailVCLM B) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongTailVCLM_apply]
  have : ‖alongTailV B' u - alongTailV B u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j' => u (Fin.cons (k 0) j')) (le_trans (norm_tailSliceV_le u _) hu)
    calc ‖(alongTailV B' u - alongTailV B u) k‖
        = ‖(B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))) (Fin.tail k)‖ := rfl
      _ ≤ ‖B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongTailV B' u - alongTailV B u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

end AlongV

section TensorV

/-- Coordinate-by-coordinate application of `d` maps to a `d`-dimensional `V`-valued
array: the lower coordinates first on every slice, then coordinate `0`. -/
def tensorV : (d : ℕ) → (N : Fin d → ℕ) →
    ((i : Fin d) → (Fin (N i) → V) → (Fin (N i) → V)) →
    (((i : Fin d) → Fin (N i)) → V) → (((i : Fin d) → Fin (N i)) → V)
  | 0, _, _ => id
  | d + 1, N, A => alongHeadV (A 0) ∘ alongTailV (tensorV d (fun i => N i.succ) fun i => A i.succ)

omit [NormedAddCommGroup V] in
theorem tensorV_zero {N : Fin 0 → ℕ} (A) (u : ((i : Fin 0) → Fin (N i)) → V) :
    tensorV 0 N A u = u := rfl

omit [NormedAddCommGroup V] in
theorem tensorV_succ {d : ℕ} {N : Fin (d + 1) → ℕ}
    (A : (i : Fin (d + 1)) → (Fin (N i) → V) → (Fin (N i) → V))
    (u : ((i : Fin (d + 1)) → Fin (N i)) → V) :
    tensorV (d + 1) N A u =
      alongHeadV (A 0) (alongTailV (tensorV d (fun i => N i.succ) fun i => A i.succ) u) := rfl

theorem tensorV_ball : ∀ (d : ℕ) (N : Fin d → ℕ)
    (A' : (i : Fin d) → (Fin (N i) → V) → (Fin (N i) → V)),
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ∀ u : ((i : Fin d) → Fin (N i)) → V, ‖u‖ ≤ 1 → ‖tensorV d N A' u‖ ≤ 1
  | 0, _, _, _, _, hu => hu
  | d + 1, N, A', hA', u, hu => by
    rw [tensorV_succ]
    exact alongHeadV_ball (hA' 0) _
      (alongTailV_ball (tensorV_ball d _ _ fun i => hA' i.succ) u hu)

variable [NormedSpace ℂ V]

/-- The exact tensor product of `d` continuous linear maps. -/
noncomputable def tensorVCLM : (d : ℕ) → (N : Fin d → ℕ) →
    ((i : Fin d) → (Fin (N i) → V) →L[ℂ] (Fin (N i) → V)) →
    (((i : Fin d) → Fin (N i)) → V) →L[ℂ] (((i : Fin d) → Fin (N i)) → V)
  | 0, _, _ => ContinuousLinearMap.id ℂ _
  | d + 1, N, A =>
    alongHeadVCLM (A 0) ∘L alongTailVCLM (tensorVCLM d (fun i => N i.succ) fun i => A i.succ)

theorem tensorVCLM_apply : ∀ (d : ℕ) (N : Fin d → ℕ)
    (A : (i : Fin d) → (Fin (N i) → V) →L[ℂ] (Fin (N i) → V))
    (u : ((i : Fin d) → Fin (N i)) → V),
    tensorVCLM d N A u = tensorV d N (fun i => (A i : (Fin (N i) → V) → (Fin (N i) → V))) u
  | 0, _, _, _ => rfl
  | d + 1, N, A, u => by
    simp only [tensorVCLM, tensorV, ContinuousLinearMap.comp_apply, Function.comp_apply,
      alongHeadVCLM_apply, alongTailVCLM_apply]
    congr 1
    funext k
    exact congrFun (tensorVCLM_apply d _ _ _) _

theorem opNorm_tensorVCLM_le : ∀ (d : ℕ) (N : Fin d → ℕ)
    (A : (i : Fin d) → (Fin (N i) → V) →L[ℂ] (Fin (N i) → V)),
    (∀ i, ‖A i‖ ≤ 1) → ‖tensorVCLM d N A‖ ≤ 1
  | 0, _, _, _ => ContinuousLinearMap.norm_id_le
  | d + 1, N, A, hA => by
    simp only [tensorVCLM]
    calc ‖alongHeadVCLM (A 0) ∘L alongTailVCLM (tensorVCLM d (fun i => N i.succ) fun i => A i.succ)‖
        ≤ ‖alongHeadVCLM (A 0)‖ *
          ‖alongTailVCLM (tensorVCLM d (fun i => N i.succ) fun i => A i.succ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact opNorm_alongHeadVCLM_le _ (hA 0)
          · exact opNorm_alongTailVCLM_le _ (opNorm_tensorVCLM_le d _ _ fun i => hA i.succ)
      _ = 1 := one_mul _

/-- Lemma 2.11 with `d` factors and `V`-valued arrays: the coordinate-by-coordinate
approximation of a tensor product has the sum of the coordinate errors. -/
theorem approxMap_tensorV {p : ℕ} : ∀ (d : ℕ) (N : Fin d → ℕ)
    (A' : (i : Fin d) → (Fin (N i) → V) → (Fin (N i) → V))
    (A : (i : Fin d) → (Fin (N i) → V) →L[ℂ] (Fin (N i) → V)) (ε : Fin d → ℝ),
    (∀ i, ‖A i‖ ≤ 1) → (∀ i, ApproxMap p (A' i) (A i) (ε i)) →
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ApproxMap p (tensorV d N A') (tensorVCLM d N A) (∑ i, ε i)
  | 0, _, _, _, _, _, _, _ => by
    intro u _
    simp [tensorV, tensorVCLM]
  | d + 1, N, A', A, ε, hA, h, hball => by
    rw [Fin.sum_univ_succ]
    exact approx_comp (opNorm_alongHeadVCLM_le _ (hA 0))
      (approxMap_alongTailV (approxMap_tensorV d _ _ _ _ (fun i => hA i.succ)
        (fun i => h i.succ) (fun i => hball i.succ)))
      (approxMap_alongHeadV (h 0))
      (fun u hu => alongTailV_ball (tensorV_ball d _ _ fun i => hball i.succ) u hu)

end TensorV

end IntegerMultBounds.NLogN

namespace IntegerMultBounds.NLogN

variable {V : Type*} [NormedAddCommGroup V]

section Rect

variable {d : ℕ}

/-- The index family after the lower coordinates have been mapped from `M` to `N` but
coordinate `0` still has length `M 0`. -/
abbrev mixFam (M N : Fin (d + 1) → ℕ) : Fin (d + 1) → ℕ :=
  Fin.cases (M 0) fun i => N i.succ

/-- Apply `A : Fin (M 0) → Fin (N 0)` along coordinate `0`, lower coordinates already at `N`. -/
def alongHeadVR {M N : Fin (d + 1) → ℕ} (A : (Fin (M 0) → V) → (Fin (N 0) → V))
    (u : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V) : ((i : Fin (d + 1)) → Fin (N i)) → V :=
  fun k => A (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k))) (k 0)

/-- Apply the lower-dimensional rectangular map `B` on every coordinate-`0` slice. -/
def alongTailVR {M N : Fin (d + 1) → ℕ}
    (B : (((i : Fin d) → Fin (M i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V))
    (u : ((i : Fin (d + 1)) → Fin (M i)) → V) : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V :=
  fun k => B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)

/-- Coordinate-by-coordinate application of `d` rectangular maps. -/
def tensorVR : (d : ℕ) → (M N : Fin d → ℕ) →
    ((i : Fin d) → (Fin (M i) → V) → (Fin (N i) → V)) →
    (((i : Fin d) → Fin (M i)) → V) → (((i : Fin d) → Fin (N i)) → V)
  | 0, _, _, _ => fun u _ => u fun i => i.elim0
  | d + 1, M, N, A =>
    alongHeadVR (A 0) ∘ alongTailVR (tensorVR d (fun i => M i.succ) (fun i => N i.succ)
      fun i => A i.succ)


variable {M N : Fin (d + 1) → ℕ}

theorem norm_headSliceVR_le (u : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V)
    (t : (i : Fin d) → Fin (N i.succ)) :
    ‖fun j₀ : Fin (M 0) => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ t)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j₀
  exact norm_le_pi_norm u _

theorem norm_tailSliceVR_le (u : ((i : Fin (d + 1)) → Fin (M i)) → V) (j₀ : Fin (M 0)) :
    ‖fun j' => u (Fin.cons j₀ j')‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j'
  exact norm_le_pi_norm u _

theorem norm_alongHeadVR_le {A : (Fin (M 0) → V) → (Fin (N 0) → V)}
    {u : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ v, ‖v‖ ≤ ‖u‖ → ‖A v‖ ≤ C) : ‖alongHeadVR A u‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  intro k
  calc ‖alongHeadVR A u k‖
      = ‖A (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k))) (k 0)‖ :=
        rfl
    _ ≤ ‖A (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k)))‖ :=
        norm_le_pi_norm _ _
    _ ≤ C := hA _ (norm_headSliceVR_le u _)

theorem norm_alongTailVR_le
    {B : (((i : Fin d) → Fin (M i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    {u : ((i : Fin (d + 1)) → Fin (M i)) → V} {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v, ‖v‖ ≤ ‖u‖ → ‖B v‖ ≤ C) : ‖alongTailVR B u‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  intro k
  calc ‖alongTailVR B u k‖ = ‖B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)‖ := rfl
    _ ≤ ‖B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
    _ ≤ C := hB _ (norm_tailSliceVR_le u _)

theorem alongHeadVR_ball {A : (Fin (M 0) → V) → (Fin (N 0) → V)}
    (hA : ∀ v, ‖v‖ ≤ 1 → ‖A v‖ ≤ 1) (u : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V)
    (hu : ‖u‖ ≤ 1) : ‖alongHeadVR A u‖ ≤ 1 :=
  norm_alongHeadVR_le zero_le_one fun v hv => hA v (le_trans hv hu)

theorem alongTailVR_ball
    {B : (((i : Fin d) → Fin (M i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    (hB : ∀ v, ‖v‖ ≤ 1 → ‖B v‖ ≤ 1) (u : ((i : Fin (d + 1)) → Fin (M i)) → V)
    (hu : ‖u‖ ≤ 1) : ‖alongTailVR B u‖ ≤ 1 :=
  norm_alongTailVR_le zero_le_one fun v hv => hB v (le_trans hv hu)

variable [NormedSpace ℂ V]

/-- Restriction to a coordinate-`0` line, as a continuous linear map. -/
noncomputable def headSliceVRCLM (t : (i : Fin d) → Fin (N i.succ)) :
    (((i : Fin (d + 1)) → Fin (mixFam M N i)) → V) →L[ℂ] (Fin (M 0) → V) :=
  ContinuousLinearMap.pi fun j₀ =>
    ContinuousLinearMap.proj (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ t)

/-- Restriction to a coordinate-`0` slice, as a continuous linear map. -/
noncomputable def tailSliceVRCLM (j₀ : Fin (M 0)) :
    (((i : Fin (d + 1)) → Fin (M i)) → V) →L[ℂ] (((i : Fin d) → Fin (M i.succ)) → V) :=
  ContinuousLinearMap.pi fun j' => ContinuousLinearMap.proj (Fin.cons j₀ j')

/-- The continuous linear rectangular action along coordinate `0`. -/
noncomputable def alongHeadVRCLM (A : (Fin (M 0) → V) →L[ℂ] (Fin (N 0) → V)) :
    (((i : Fin (d + 1)) → Fin (mixFam M N i)) → V) →L[ℂ] (((i : Fin (d + 1)) → Fin (N i)) → V) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (k 0)).comp (A.comp (headSliceVRCLM (Fin.tail k)))

/-- The continuous linear slice-wise action of a lower-dimensional rectangular map. -/
noncomputable def alongTailVRCLM
    (B : (((i : Fin d) → Fin (M i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V)) :
    (((i : Fin (d + 1)) → Fin (M i)) → V) →L[ℂ] (((i : Fin (d + 1)) → Fin (mixFam M N i)) → V) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (Fin.tail k)).comp (B.comp (tailSliceVRCLM (k 0)))

theorem alongHeadVRCLM_apply (A : (Fin (M 0) → V) →L[ℂ] (Fin (N 0) → V))
    (u : ((i : Fin (d + 1)) → Fin (mixFam M N i)) → V) :
    alongHeadVRCLM A u = alongHeadVR A u := by
  funext k
  simp [alongHeadVRCLM, headSliceVRCLM, alongHeadVR]

theorem alongTailVRCLM_apply
    (B : (((i : Fin d) → Fin (M i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V))
    (u : ((i : Fin (d + 1)) → Fin (M i)) → V) : alongTailVRCLM B u = alongTailVR B u := by
  funext k
  rfl

theorem opNorm_alongHeadVRCLM_le (A : (Fin (M 0) → V) →L[ℂ] (Fin (N 0) → V))
    (hA : ‖A‖ ≤ 1) : ‖alongHeadVRCLM (d := d) (M := M) (N := N) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongHeadVRCLM_apply, one_mul]
  apply norm_alongHeadVR_le (norm_nonneg _)
  intro v hv
  calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem opNorm_alongTailVRCLM_le
    (B : (((i : Fin d) → Fin (M i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V))
    (hB : ‖B‖ ≤ 1) : ‖alongTailVRCLM (M := M) (N := N) B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongTailVRCLM_apply, one_mul]
  apply norm_alongTailVR_le (norm_nonneg _)
  intro v hv
  calc ‖B v‖ ≤ ‖B‖ * ‖v‖ := B.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem approxMap_alongHeadVR {p : ℕ} {A' : (Fin (M 0) → V) → (Fin (N 0) → V)}
    {A : (Fin (M 0) → V) →L[ℂ] (Fin (N 0) → V)} {ε : ℝ} (h : ApproxMap p A' A ε) :
    ApproxMap p (alongHeadVR (d := d) A') (alongHeadVRCLM A) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongHeadVRCLM_apply]
  have : ‖alongHeadVR A' u - alongHeadVR A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k)))
      (le_trans (norm_headSliceVR_le u _) hu)
    calc ‖(alongHeadVR A' u - alongHeadVR A u) k‖
        = ‖(A' (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k))))
            (k 0)‖ := rfl
      _ ≤ ‖A' (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons (α := fun i => Fin (mixFam M N i)) j₀ (Fin.tail k)))‖ :=
          norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongHeadVR A' u - alongHeadVR A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

theorem approxMap_alongTailVR {p : ℕ}
    {B' : (((i : Fin d) → Fin (M i.succ)) → V) → (((i : Fin d) → Fin (N i.succ)) → V)}
    {B : (((i : Fin d) → Fin (M i.succ)) → V) →L[ℂ] (((i : Fin d) → Fin (N i.succ)) → V)}
    {ε : ℝ} (h : ApproxMap p B' B ε) :
    ApproxMap p (alongTailVR (M := M) (N := N) B') (alongTailVRCLM B) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongTailVRCLM_apply]
  have : ‖alongTailVR B' u - alongTailVR B u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j' => u (Fin.cons (k 0) j')) (le_trans (norm_tailSliceVR_le u _) hu)
    calc ‖(alongTailVR B' u - alongTailVR B u) k‖
        = ‖(B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))) (Fin.tail k)‖ := rfl
      _ ≤ ‖B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongTailVR B' u - alongTailVR B u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

end Rect

section TensorVR

variable [NormedSpace ℂ V]

/-- The exact tensor product of `d` rectangular continuous linear maps. -/
noncomputable def tensorVRCLM : (d : ℕ) → (M N : Fin d → ℕ) →
    ((i : Fin d) → (Fin (M i) → V) →L[ℂ] (Fin (N i) → V)) →
    (((i : Fin d) → Fin (M i)) → V) →L[ℂ] (((i : Fin d) → Fin (N i)) → V)
  | 0, _, _, _ => ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj fun i => i.elim0
  | d + 1, M, N, A =>
    alongHeadVRCLM (A 0) ∘L
      alongTailVRCLM (tensorVRCLM d (fun i => M i.succ) (fun i => N i.succ) fun i => A i.succ)

theorem tensorVRCLM_apply : ∀ (d : ℕ) (M N : Fin d → ℕ)
    (A : (i : Fin d) → (Fin (M i) → V) →L[ℂ] (Fin (N i) → V))
    (u : ((i : Fin d) → Fin (M i)) → V),
    tensorVRCLM d M N A u = tensorVR d M N (fun i => (A i : (Fin (M i) → V) → (Fin (N i) → V))) u
  | 0, _, _, _, _ => by
    funext k
    simp [tensorVRCLM, tensorVR]
  | d + 1, M, N, A, u => by
    simp only [tensorVRCLM, tensorVR, ContinuousLinearMap.comp_apply, Function.comp_apply,
      alongHeadVRCLM_apply, alongTailVRCLM_apply]
    congr 1
    funext k
    exact congrFun (tensorVRCLM_apply d _ _ _ _) _

omit [NormedSpace ℂ V] in
theorem tensorVR_ball : ∀ (d : ℕ) (M N : Fin d → ℕ)
    (A' : (i : Fin d) → (Fin (M i) → V) → (Fin (N i) → V)),
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ∀ u : ((i : Fin d) → Fin (M i)) → V, ‖u‖ ≤ 1 → ‖tensorVR d M N A' u‖ ≤ 1
  | 0, _, _, _, _, u, hu => by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    exact le_trans (norm_le_pi_norm u _) hu
  | d + 1, M, N, A', hA', u, hu =>
    alongHeadVR_ball (hA' 0) _
      (alongTailVR_ball (tensorVR_ball d _ _ _ fun i => hA' i.succ) u hu)

theorem opNorm_tensorVRCLM_le : ∀ (d : ℕ) (M N : Fin d → ℕ)
    (A : (i : Fin d) → (Fin (M i) → V) →L[ℂ] (Fin (N i) → V)),
    (∀ i, ‖A i‖ ≤ 1) → ‖tensorVRCLM d M N A‖ ≤ 1
  | 0, _, _, A, _ => by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    simp only [tensorVRCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm u _
  | d + 1, M, N, A, hA => by
    simp only [tensorVRCLM]
    calc ‖alongHeadVRCLM (A 0) ∘L
          alongTailVRCLM (tensorVRCLM d (fun i => M i.succ) (fun i => N i.succ) fun i => A i.succ)‖
        ≤ ‖alongHeadVRCLM (A 0)‖ *
          ‖alongTailVRCLM (tensorVRCLM d (fun i => M i.succ) (fun i => N i.succ)
            fun i => A i.succ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact opNorm_alongHeadVRCLM_le _ (hA 0)
          · exact opNorm_alongTailVRCLM_le _ (opNorm_tensorVRCLM_le d _ _ _ fun i => hA i.succ)
      _ = 1 := one_mul _

/-- Lemma 2.11 for rectangular maps between arrays of different shapes. -/
theorem approxMap_tensorVR {p : ℕ} : ∀ (d : ℕ) (M N : Fin d → ℕ)
    (A' : (i : Fin d) → (Fin (M i) → V) → (Fin (N i) → V))
    (A : (i : Fin d) → (Fin (M i) → V) →L[ℂ] (Fin (N i) → V)) (ε : Fin d → ℝ),
    (∀ i, ‖A i‖ ≤ 1) → (∀ i, ApproxMap p (A' i) (A i) (ε i)) →
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ApproxMap p (tensorVR d M N A') (tensorVRCLM d M N A) (∑ i, ε i)
  | 0, _, _, _, _, _, _, _, _ => by
    intro u _
    simp [tensorVR, tensorVRCLM]
  | d + 1, M, N, A', A, ε, hA, h, hball => by
    rw [Fin.sum_univ_succ]
    exact approx_comp (opNorm_alongHeadVRCLM_le _ (hA 0))
      (approxMap_alongTailVR (approxMap_tensorVR d _ _ _ _ _ (fun i => hA i.succ)
        (fun i => h i.succ) (fun i => hball i.succ)))
      (approxMap_alongHeadVR (h 0))
      (fun u hu => alongTailVR_ball (tensorVR_ball d _ _ _ fun i => hball i.succ) u hu)

end TensorVR


end IntegerMultBounds.NLogN
