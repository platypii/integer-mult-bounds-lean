module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowAssembly
public import IntegerMultBounds.NLogN.Approx

/-! Covered core certificates supply the normalized operator contract. A half-unit
slack proves preservation of the unit ball without an extra rounding operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem publishedWindows_operator_spec (p : ℕ) (A : (ι → ℂ) →L[ℂ] (κ → ℂ))
    (ws : List (Window κ)) (localOut : Window κ → (ι → ℂ) → κ → ℂ)
    (initial : (ι → ℂ) → κ → ℂ) (error : ℝ) (he : 0 ≤ error)
    (hcover : ∀ i, ∃ w ∈ ws, i ∈ w.core)
    (hlocal : ∀ w ∈ ws, ∀ u, ‖u‖ ≤ 1 → ErrorOn w.core (localOut w u) (A u) (error/2^p))
    (hA : ‖A‖ ≤ 1/2) (hsmall : error/2^p ≤ 1/2) :
    ApproxMap p (fun u => publishWindows (fun w => localOut w u) ws (initial u)) A error ∧
      ∀ u, ‖u‖ ≤ 1 → ‖publishWindows (fun w => localOut w u) ws (initial u)‖ ≤ 1 := by
  have herr (u : ι → ℂ) (hu : ‖u‖ ≤ 1) :
      ‖publishWindows (fun w => localOut w u) ws (initial u)-A u‖ ≤ error/2^p := by
    apply norm_error_of_publish ws (fun w => localOut w u) _ (A u) _ (by positivity)
      (fun w hw => hlocal w hw u hu)
    intro i
    exact publishWindows_source (fun w => localOut w u) ws (initial u) i (hcover i)
  constructor
  · intro u hu
    have hp : (0 : ℝ) < 2^p := by positivity
    have h := (mul_le_mul_of_nonneg_left (herr u hu) hp.le)
    simpa only [mul_div_cancel₀ _ (ne_of_gt hp)] using h
  · intro u hu
    have hAu : ‖A u‖ ≤ (1/2 : ℝ) := by
      calc
        ‖A u‖ ≤ ‖A‖*‖u‖ := A.le_opNorm u
        _ ≤ (1/2 : ℝ)*1 := mul_le_mul hA hu (norm_nonneg _) (by norm_num)
        _ = 1/2 := by ring
    have hsum := norm_add_le
      (publishWindows (fun w => localOut w u) ws (initial u)-A u) (A u)
    rw [sub_add_cancel] at hsum
    exact hsum.trans ((add_le_add (herr u hu) hAu).trans (by linarith))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
