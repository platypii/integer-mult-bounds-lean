import IntegerMultBounds.NLogN.TensorApprox
import IntegerMultBounds.NLogN.MultidimD

/-! The `d`-fold form of Lemma 2.11 of Harvey and van der Hoeven. Proved:
applying a map along the first coordinate of a `d + 1`-dimensional array, or a
lower-dimensional map on every first-coordinate slice, keeps unit norms and
approximation errors; the coordinate-by-coordinate tensor of approximations
approximates the tensor of the exact maps with the sum of the errors; and the
`d`-dimensional transform, normalized or not, is exactly the tensor of the
one-dimensional transforms. No cost model is attached. -/

open Complex

namespace IntegerMultBounds.NLogN

section Along

variable {d : ℕ} {N : Fin (d + 1) → ℕ}

/-- Apply `A` along coordinate `0` of a `d + 1`-dimensional array. -/
def alongHead (A : (ZMod (N 0) → ℂ) → (ZMod (N 0) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ :=
  fun k => A (fun j₀ => u (Fin.cons j₀ (Fin.tail k))) (k 0)

/-- Apply the lower-dimensional map `B` on every coordinate-`0` slice. -/
def alongTail (B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ :=
  fun k => B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)

variable [∀ i, NeZero (N i)]

theorem norm_headSlice_le (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ)
    (t : (i : Fin d) → ZMod (N i.succ)) :
    ‖fun j₀ => u (Fin.cons j₀ t)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j₀
  exact norm_le_pi_norm u _

theorem norm_tailSlice_le (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) (j₀ : ZMod (N 0)) :
    ‖fun j' => u (Fin.cons j₀ j')‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j'
  exact norm_le_pi_norm u _

theorem norm_alongHead_le {A : (ZMod (N 0) → ℂ) → (ZMod (N 0) → ℂ)}
    {u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ v, ‖v‖ ≤ ‖u‖ → ‖A v‖ ≤ M) : ‖alongHead A u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro k
  calc ‖alongHead A u k‖ = ‖A (fun j₀ => u (Fin.cons j₀ (Fin.tail k))) (k 0)‖ := rfl
    _ ≤ ‖A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))‖ := norm_le_pi_norm _ _
    _ ≤ M := hA _ (norm_headSlice_le u _)

theorem norm_alongTail_le
    {B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ v, ‖v‖ ≤ ‖u‖ → ‖B v‖ ≤ M) : ‖alongTail B u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro k
  calc ‖alongTail B u k‖ = ‖B (fun j' => u (Fin.cons (k 0) j')) (Fin.tail k)‖ := rfl
    _ ≤ ‖B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
    _ ≤ M := hB _ (norm_tailSlice_le u _)

theorem alongHead_ball {A : (ZMod (N 0) → ℂ) → (ZMod (N 0) → ℂ)}
    (hA : ∀ v, ‖v‖ ≤ 1 → ‖A v‖ ≤ 1) (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ)
    (hu : ‖u‖ ≤ 1) : ‖alongHead A u‖ ≤ 1 :=
  norm_alongHead_le zero_le_one fun v hv => hA v (le_trans hv hu)

theorem alongTail_ball
    {B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    (hB : ∀ v, ‖v‖ ≤ 1 → ‖B v‖ ≤ 1) (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ)
    (hu : ‖u‖ ≤ 1) : ‖alongTail B u‖ ≤ 1 :=
  norm_alongTail_le zero_le_one fun v hv => hB v (le_trans hv hu)

/-- Restriction to a coordinate-`0` line, as a continuous linear map. -/
noncomputable def headSliceCLM (t : (i : Fin d) → ZMod (N i.succ)) :
    (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ) :=
  ContinuousLinearMap.pi fun j₀ => ContinuousLinearMap.proj (Fin.cons j₀ t)

/-- Restriction to a coordinate-`0` slice, as a continuous linear map. -/
noncomputable def tailSliceCLM (j₀ : ZMod (N 0)) :
    (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ) :=
  ContinuousLinearMap.pi fun j' => ContinuousLinearMap.proj (Fin.cons j₀ j')

/-- The continuous linear action along coordinate `0`. -/
noncomputable def alongHeadCLM (A : (ZMod (N 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ)) :
    (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (k 0)).comp (A.comp (headSliceCLM (Fin.tail k)))

/-- The continuous linear slice-wise action of a lower-dimensional map. -/
noncomputable def alongTailCLM
    (B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ)) :
    (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin (d + 1)) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (Fin.tail k)).comp (B.comp (tailSliceCLM (k 0)))

omit [∀ i, NeZero (N i)] in
theorem alongHeadCLM_apply (A : (ZMod (N 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) : alongHeadCLM A u = alongHead A u := by
  funext k
  simp [alongHeadCLM, headSliceCLM, alongHead]

omit [∀ i, NeZero (N i)] in
theorem alongTailCLM_apply
    (B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) : alongTailCLM B u = alongTail B u := by
  funext k
  simp [alongTailCLM, tailSliceCLM, alongTail]

theorem opNorm_alongHeadCLM_le (A : (ZMod (N 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ))
    (hA : ‖A‖ ≤ 1) : ‖alongHeadCLM (d := d) (N := N) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongHeadCLM_apply, one_mul]
  apply norm_alongHead_le (norm_nonneg _)
  intro v hv
  calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem opNorm_alongTailCLM_le
    (B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ))
    (hB : ‖B‖ ≤ 1) : ‖alongTailCLM (N := N) B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [alongTailCLM_apply, one_mul]
  apply norm_alongTail_le (norm_nonneg _)
  intro v hv
  calc ‖B v‖ ≤ ‖B‖ * ‖v‖ := B.le_opNorm v
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem approxMap_alongHead {p : ℕ} {A' : (ZMod (N 0) → ℂ) → (ZMod (N 0) → ℂ)}
    {A : (ZMod (N 0) → ℂ) →L[ℂ] (ZMod (N 0) → ℂ)} {ε : ℝ} (h : ApproxMap p A' A ε) :
    ApproxMap p (alongHead (d := d) A') (alongHeadCLM A) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongHeadCLM_apply]
  have : ‖alongHead A' u - alongHead A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
      (le_trans (norm_headSlice_le u _) hu)
    calc ‖(alongHead A' u - alongHead A u) k‖
        = ‖(A' (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))) (k 0)‖ := rfl
      _ ≤ ‖A' (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))
            - A (fun j₀ => u (Fin.cons j₀ (Fin.tail k)))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongHead A' u - alongHead A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

theorem approxMap_alongTail {p : ℕ}
    {B' : (((i : Fin d) → ZMod (N i.succ)) → ℂ) → (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {B : (((i : Fin d) → ZMod (N i.succ)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i.succ)) → ℂ)}
    {ε : ℝ} (h : ApproxMap p B' B ε) :
    ApproxMap p (alongTail (N := N) B') (alongTailCLM B) ε := by
  intro u hu
  have hε : 0 ≤ ε := le_trans (by positivity) (h 0 (by simp))
  rw [alongTailCLM_apply]
  have : ‖alongTail B' u - alongTail B u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hk := h (fun j' => u (Fin.cons (k 0) j')) (le_trans (norm_tailSlice_le u _) hu)
    calc ‖(alongTail B' u - alongTail B u) k‖
        = ‖(B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))) (Fin.tail k)‖ := rfl
      _ ≤ ‖B' (fun j' => u (Fin.cons (k 0) j'))
            - B (fun j' => u (Fin.cons (k 0) j'))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc (2 : ℝ) ^ p * ‖alongTail B' u - alongTail B u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

end Along

section TensorD

/-- Coordinate-by-coordinate application of `d` maps to a `d`-dimensional array:
the lower coordinates first on every slice, then coordinate `0`. -/
def tensorD : (d : ℕ) → (N : Fin d → ℕ) →
    ((i : Fin d) → (ZMod (N i) → ℂ) → (ZMod (N i) → ℂ)) →
    (((i : Fin d) → ZMod (N i)) → ℂ) → (((i : Fin d) → ZMod (N i)) → ℂ)
  | 0, _, _ => id
  | d + 1, N, A => alongHead (A 0) ∘ alongTail (tensorD d (fun i => N i.succ) fun i => A i.succ)

/-- The exact tensor product of `d` continuous linear maps. -/
noncomputable def tensorDCLM : (d : ℕ) → (N : Fin d → ℕ) →
    ((i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) →
    (((i : Fin d) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i)) → ℂ)
  | 0, _, _ => ContinuousLinearMap.id ℂ _
  | d + 1, N, A =>
    alongHeadCLM (A 0) ∘L alongTailCLM (tensorDCLM d (fun i => N i.succ) fun i => A i.succ)

theorem tensorD_zero {N : Fin 0 → ℕ} (A) (u : ((i : Fin 0) → ZMod (N i)) → ℂ) :
    tensorD 0 N A u = u := rfl

theorem tensorD_succ {d : ℕ} {N : Fin (d + 1) → ℕ}
    (A : (i : Fin (d + 1)) → (ZMod (N i) → ℂ) → (ZMod (N i) → ℂ))
    (u : ((i : Fin (d + 1)) → ZMod (N i)) → ℂ) :
    tensorD (d + 1) N A u =
      alongHead (A 0) (alongTail (tensorD d (fun i => N i.succ) fun i => A i.succ) u) := rfl

theorem tensorDCLM_apply : ∀ (d : ℕ) (N : Fin d → ℕ)
    (A : (i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (u : ((i : Fin d) → ZMod (N i)) → ℂ),
    tensorDCLM d N A u = tensorD d N (fun i => (A i : (ZMod (N i) → ℂ) → (ZMod (N i) → ℂ))) u
  | 0, _, _, _ => rfl
  | d + 1, N, A, u => by
    simp only [tensorDCLM, tensorD, ContinuousLinearMap.comp_apply, Function.comp_apply,
      alongHeadCLM_apply, alongTailCLM_apply]
    congr 1
    funext k
    exact congrFun (tensorDCLM_apply d _ _ _) _

theorem tensorD_ball : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (A' : (i : Fin d) → (ZMod (N i) → ℂ) → (ZMod (N i) → ℂ)),
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ∀ u : ((i : Fin d) → ZMod (N i)) → ℂ, ‖u‖ ≤ 1 → ‖tensorD d N A' u‖ ≤ 1
  | 0, _, _, _, _, _, hu => hu
  | d + 1, N, _, A', hA', u, hu => by
    rw [tensorD_succ]
    exact alongHead_ball (hA' 0) _
      (alongTail_ball (tensorD_ball d _ _ fun i => hA' i.succ) u hu)

theorem opNorm_tensorDCLM_le : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (A : (i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)),
    (∀ i, ‖A i‖ ≤ 1) → ‖tensorDCLM d N A‖ ≤ 1
  | 0, _, _, _, _ => ContinuousLinearMap.norm_id_le
  | d + 1, N, _, A, hA => by
    simp only [tensorDCLM]
    calc ‖alongHeadCLM (A 0) ∘L alongTailCLM (tensorDCLM d (fun i => N i.succ) fun i => A i.succ)‖
        ≤ ‖alongHeadCLM (A 0)‖ *
          ‖alongTailCLM (tensorDCLM d (fun i => N i.succ) fun i => A i.succ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact opNorm_alongHeadCLM_le _ (hA 0)
          · exact opNorm_alongTailCLM_le _ (opNorm_tensorDCLM_le d _ _ fun i => hA i.succ)
      _ = 1 := one_mul _

/-- Lemma 2.11 with `d` factors: the coordinate-by-coordinate approximation of a tensor
product has the sum of the coordinate errors. -/
theorem approxMap_tensorD {p : ℕ} : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (A' : (i : Fin d) → (ZMod (N i) → ℂ) → (ZMod (N i) → ℂ))
    (A : (i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) (ε : Fin d → ℝ),
    (∀ i, ‖A i‖ ≤ 1) → (∀ i, ApproxMap p (A' i) (A i) (ε i)) →
    (∀ i v, ‖v‖ ≤ 1 → ‖A' i v‖ ≤ 1) →
    ApproxMap p (tensorD d N A') (tensorDCLM d N A) (∑ i, ε i)
  | 0, _, _, _, _, _, _, _, _ => by
    intro u _
    simp [tensorD, tensorDCLM]
  | d + 1, N, _, A', A, ε, hA, h, hball => by
    rw [Fin.sum_univ_succ]
    exact approx_comp (opNorm_alongHeadCLM_le _ (hA 0))
      (approxMap_alongTail (approxMap_tensorD d _ _ _ _ (fun i => hA i.succ)
        (fun i => h i.succ) (fun i => hball i.succ)))
      (approxMap_alongHead (h 0))
      (fun u hu => alongTail_ball (tensorD_ball d _ _ fun i => hball i.succ) u hu)

end TensorD

section DFT

/-- The `d`-dimensional transform is the tensor of the one-dimensional transforms. -/
theorem dftD_eq_tensorD : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)] (ζ : Fin d → ℂ)
    (a : ((i : Fin d) → ZMod (N i)) → ℂ),
    dftD ζ a = tensorD d N (fun i => dft (ζ i)) a
  | 0, N, _, ζ, a => by
    funext k
    simp only [dftD, Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero, one_mul,
      tensorD, id]
    exact congrArg _ (Subsingleton.elim _ _)
  | d + 1, N, _, ζ, a => by
    rw [dftD_succ, tensorD_succ]
    funext k
    simp only [alongHead, alongTail, Fin.cons_zero, Fin.tail_cons]
    congr 1
    funext j₀
    exact congrFun (dftD_eq_tensorD d (fun i => N i.succ) (Fin.tail ζ)
      (fun j' => a (Fin.cons j₀ j'))) (Fin.tail k)

/-- The normalized `d`-dimensional transform is the tensor of the normalized
one-dimensional transforms. -/
theorem dftD_norm_eq_tensorD : ∀ (d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)] (ζ : Fin d → ℂ)
    (a : ((i : Fin d) → ZMod (N i)) → ℂ),
    (fun k => (1 / ((∏ i, N i : ℕ) : ℂ)) * dftD ζ a k) =
      tensorD d N (fun i => dftNormZ (N i) (ζ i)) a
  | 0, N, _, ζ, a => by
    funext k
    simp only [dftD, Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero, one_mul,
      tensorD, id, Nat.cast_one, div_one]
    exact congrArg _ (Subsingleton.elim _ _)
  | d + 1, N, _, ζ, a => by
    rw [dftD_succ, tensorD_succ]
    funext k
    simp only [alongHead, alongTail, Fin.cons_zero, Fin.tail_cons, dftNormZ]
    have ih : ∀ j₀, (fun j' => dftD (Fin.tail ζ) (fun j' => a (Fin.cons j₀ j')) j') =
        (fun j' => ((∏ i : Fin d, N i.succ : ℕ) : ℂ) *
          tensorD d (fun i => N i.succ) (fun i => dftNormZ (N i.succ) (ζ i.succ))
            (fun j' => a (Fin.cons j₀ j')) j') := by
      intro j₀
      have h := dftD_norm_eq_tensorD d (fun i => N i.succ) (Fin.tail ζ)
        (fun j' => a (Fin.cons j₀ j'))
      funext j'
      have hP : ((∏ i : Fin d, N i.succ : ℕ) : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne _
      have e : tensorD d (fun i => N i.succ) (fun i => dftNormZ (N i.succ) (ζ i.succ))
          (fun j' => a (Fin.cons j₀ j')) j' =
          1 / ((∏ i : Fin d, N i.succ : ℕ) : ℂ) *
            dftD (Fin.tail ζ) (fun j' => a (Fin.cons j₀ j')) j' := (congrFun h j').symm
      rw [e]
      field_simp
    simp_rw [ih]
    have hs : (fun j₀ => ((∏ i : Fin d, N i.succ : ℕ) : ℂ) *
        tensorD d (fun i => N i.succ) (fun i => dftNormZ (N i.succ) (ζ i.succ))
          (fun j' => a (Fin.cons j₀ j')) (Fin.tail k)) =
        ((∏ i : Fin d, N i.succ : ℕ) : ℂ) • (fun j₀ =>
        tensorD d (fun i => N i.succ) (fun i => dftNormZ (N i.succ) (ζ i.succ))
          (fun j' => a (Fin.cons j₀ j')) (Fin.tail k)) := by
      funext j₀; simp [smul_eq_mul]
    rw [hs, dft_smul, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_succ]
    push_cast
    have h0 : ((N 0 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have hP : (∏ i : Fin d, ((N i.succ : ℕ) : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (NeZero.ne _)
    field_simp

end DFT

end IntegerMultBounds.NLogN
