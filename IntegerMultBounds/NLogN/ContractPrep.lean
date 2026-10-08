import IntegerMultBounds.NLogN.MainTransform
import IntegerMultBounds.NLogN.ExplicitNumeric

/-! The recursive step with the resampling side made explicit. Every
hypothesis of `main_step_full` about the resampling maps is discharged by the
explicit numerical maps of `ExplicitNumeric.lean` at window size `m = p`: the
left inverses `J_i` are chosen from `exists_left_inverse`, the per-coordinate
maps are `clampV ∘ resampANum` and `clampV ∘ resampBNumC`, and their errors
`(8p + 7)/2` and `(24p + 23)/2` are below `p²`. What remains as a hypothesis
is the prime choice `s` with `s_i < t_i` coprime and `α²(t_i/s_i − 1) ≥ 1`,
the size conditions `S ≤ T < 2S`, and a numerical power-of-two transform with
scaled error at most `8 T log₂ T` and unit-ball outputs. The bit cost of the
step is not modeled; `eps_ft_shape` records the arithmetic that turns the
Section 3 error constant into that bound. -/

namespace IntegerMultBounds.NLogN

open scoped BigOperators

section Params

variable {d n : ℕ}

/-- The parameter facts used to instantiate the explicit resampling maps at
`m = p`: `α ≥ 1`, `α² ≤ p`, `p α² ≤ p²`, and `13 ≤ p`. -/
theorem params_ok (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    (1 : ℝ) ≤ ((alphaParam d n : ℕ) : ℝ) ∧
      ((alphaParam d n : ℕ) : ℝ) ^ 2 ≤ (precision n : ℝ) ∧
      (precision n : ℝ) * ((alphaParam d n : ℕ) : ℝ) ^ 2 ≤ (precision n : ℝ) ^ 2 ∧
      13 ≤ precision n := by
  have hb := chunkSize_ge_4096 hd hn
  have hp := precision_ge hd hn
  have hα2 := alphaParam_ge_two (d := d) (n := n) (by omega) (by omega)
  have hα : (1 : ℝ) ≤ ((alphaParam d n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ alphaParam d n)
  have hαp : ((alphaParam d n : ℕ) : ℝ) ^ 2 ≤ (precision n : ℝ) := by
    have := alphaParam_sq_lt_precision hd hn
    exact_mod_cast this.le
  refine ⟨hα, hαp, ?_, by omega⟩
  have hp0 : (0 : ℝ) ≤ (precision n : ℝ) := by positivity
  calc (precision n : ℝ) * ((alphaParam d n : ℕ) : ℝ) ^ 2
      ≤ (precision n : ℝ) * (precision n : ℝ) := by gcongr
    _ = (precision n : ℝ) ^ 2 := by ring

end Params

section Explicit

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The explicit numerical `Ã_i` at window size `p`, clamped into the unit ball. -/
noncomputable def resampANumX (p : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (α : ℝ) (i : Fin d) : (ZMod (s i) → ℂ) → (ZMod (t i) → ℂ) :=
  clampV ∘ resampANum (s i) (t i) p (resampTermNum p (s i) (t i) α)

/-- The explicit numerical `B̃_i` at window size `p`, clamped into the unit ball. -/
noncomputable def resampBNumX (p : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (α : ℝ) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (i : Fin d) :
    (ZMod (t i) → ℂ) → (ZMod (s i) → ℂ) :=
  clampV ∘ resampBNumC p p (s i) (t i) α (hcop i)

theorem resampANumX_ball (p : ℕ) (α : ℝ) (i : Fin d) (v : ZMod (s i) → ℂ) :
    ‖resampANumX p s t α i v‖ ≤ 1 :=
  clamp_ball _ v

theorem resampBNumX_ball (p : ℕ) (α : ℝ) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (i : Fin d)
    (v : ZMod (t i) → ℂ) : ‖resampBNumX p s t α hcop i v‖ ≤ 1 :=
  clamp_ball _ v

/-- The per-coordinate approximation facts for `Ã_i`, with the explicit error. -/
theorem approxMap_resampANumX {p : ℕ} {α : ℝ} (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (p : ℝ) ^ 2) (hp1 : 1 ≤ p) (i : Fin d) :
    ApproxMap p (resampANumX p s t α i) (resampA (s i) (t i) α) ((4 * (2 * p + 1) + 3) / 2) :=
  approxMap_clamp (opNorm_resampA_le hα) (approxMap_resampANum_explicit hα hαp hm hp1)

/-- The per-coordinate approximation facts for `B̃_i`, with the explicit error. -/
theorem approxMap_resampBNumX {p : ℕ} {α : ℝ} (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1))
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) α) = 1)
    (hJ' : ∀ i, (1 + offDiagCLM (s i) (t i) α) ∘L J i = 1) (i : Fin d) :
    ApproxMap p (resampBNumX p s t α hcop i) (resampB (s i) (t i) α (hcop i) (J i))
      ((6 + (2 * ((6 * (2 * p) + 6) + 2) + 1)) / 2) :=
  approxMap_clamp (resampling_factorization_explicit (hst i) (hcop i) hα (hθ i) (J i) (hJ i)).2.2
    (approxMap_resampBNumC (hst i) (hcop i) (by linarith) (hθ i) (by omega) (hJ' i))

end Explicit

section Step

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- The recursive step with the explicit resampling maps: given the paper's
parameters, a coprime prime grid `s` below the power-of-two grid `t` with the
decay condition, and a numerical power-of-two transform `Ft'` with scaled error
at most `8 T log₂ T`, the rounded output is the exact product. The left inverses
`J_i` exist by `exists_left_inverse` and are chosen inside the proof. -/
theorem main_step_explicit {n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (hs : Pairwise (Function.onFun Nat.Coprime s))
    (hS : ∏ i, s i ≤ transformSize n) (hS2 : transformSize n < 2 * ∏ i, s i)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hθ : ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1))
    (Ft' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ)) {εFt : ℝ}
    (hFt : ApproxMap (precision n) Ft' (dftDCLM t) εFt)
    (hFt'ball : ∀ u, ‖u‖ ≤ 1 → ‖Ft' u‖ ≤ 1)
    (hεFt : εFt ≤ 8 * (transformSize n : ℝ) * (Nat.log 2 (transformSize n) : ℝ)) :
    evalBase (2 ^ chunkSize n) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * chunkSize n) * (∏ i, s i : ℕ)) *
        approxConvS hs (precision n) (chunkSize n)
          (mainTransformNum (gammaParam d n + 2 * d)
            (resampANumX (precision n) s t (alphaParam d n : ℝ))
            (resampBNumX (precision n) s t (alphaParam d n : ℝ) hcop) Ft')
          (fun v => negVec (mainTransformNum (gammaParam d n + 2 * d)
            (resampANumX (precision n) s t (alphaParam d n : ℝ))
            (resampBNumX (precision n) s t (alphaParam d n : ℝ) hcop) Ft' v))
          (digitsOf (chunkSize n) x) (digitsOf (chunkSize n) y)
          (i.val : ZMod (∏ i, s i))).re).toNat)
      = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨hα, hαp, hm, hp13⟩ := params_ok hd hn
  have hα0 : (0 : ℝ) < ((alphaParam d n : ℕ) : ℝ) := by linarith
  have hex : ∀ i, ∃ J : (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ),
      J ∘L (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) = 1 ∧
        (1 + offDiagCLM (s i) (t i) (alphaParam d n : ℝ)) ∘L J = 1 ∧ ‖J‖ ≤ 2 :=
    fun i => exists_left_inverse (hst i) hα0 (hθ i)
  choose J hJ hJ' _ using hex
  have hp5 : 5 ≤ precision n := by omega
  have hεA := (errA_explicit_lt_sq (p := precision n) (m := precision n) le_rfl hp5).le
  have hεB := (errB_explicit_lt_sq (p := precision n) (m := precision n) le_rfl hp13).le
  exact main_step_full hd hn hx hy hs hS hS2 hst hcop hθ J hJ
    (resampANumX (precision n) s t (alphaParam d n : ℝ))
    (resampBNumX (precision n) s t (alphaParam d n : ℝ) hcop)
    (approxMap_resampANumX hα hαp hm (by omega))
    (approxMap_resampBNumX hst hcop hα hθ J hJ hJ')
    (fun i v _ => resampANumX_ball _ _ i v) (fun i v _ => resampBNumX_ball _ _ hcop i v)
    Ft' hFt hFt'ball hεA hεB hεFt

end Step

section Cost

/-- The explicit recursive step evaluates the power-of-two transform three
times: two forward transforms and one inverse. Recorded for the cost model. -/
def mainStepTransformCalls : ℕ := 3

/-- The shape of the Section 3 error constant: `3 T′ L + 8 T′ + 4` is at most
`8 T log₂ T` for `T = T′ r` with `r ≥ 2`, `T′ ≥ 1`, and `1 ≤ L ≤ log₂ T`. -/
theorem eps_ft_shape {T' r L : ℕ} (hr : 2 ≤ r) (hL : 1 ≤ L) (hL' : L ≤ Nat.log 2 (T' * r))
    (hT' : 1 ≤ T') :
    3 * T' * L + 8 * T' + 4 ≤ 8 * (T' * r) * Nat.log 2 (T' * r) := by
  have h1 : 4 ≤ 4 * T' * L := by nlinarith
  have h2 : 8 * T' ≤ 8 * T' * L := by nlinarith
  have h3 : 16 * T' * L ≤ 8 * (T' * r) * L := by nlinarith
  have h4 : 8 * (T' * r) * L ≤ 8 * (T' * r) * Nat.log 2 (T' * r) := by
    exact Nat.mul_le_mul_left _ hL'
  nlinarith [h1, h2, h3, h4]

end Cost

end IntegerMultBounds.NLogN
