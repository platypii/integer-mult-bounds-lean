module

public import IntegerMultBounds.MathlibTM2.Mult.B0Generic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexInputWord

/-! A p-grid inverse realization extends to the normalized operator with its input rounding paid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0
open IntegerMultBounds IntegerMultBounds.NLogN ContinuousLinearMap
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

theorem resampB₀Of_grid_spec (p j : ℕ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖ ≤ 4*(p : ℝ)) (hj : 4*(p : ℝ) ≤ 2^j)
    (compute : (ZMod s → GaussianInt) → ZMod s → ℂ) (ε : ℝ)
    (hgrid : ∀ F : ZMod s → GaussianInt, (∀ i, ‖value p (F i)‖ ≤ 1) →
      ‖compute F‖ ≤ 1 ∧ 2^p*‖compute F-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • fun i => value p (F i))‖ ≤ ε)
    (df : ZMod s → ℝ) (hdf : ∀ i, 2^p*‖rhoC p (df i : ℂ)-(dPrime s t α i : ℂ)‖ ≤ 2)
    (hdf1 : ∀ i, ‖rhoC p (df i : ℂ)‖ ≤ 1) :
    ApproxMap p (resampB₀Of (t := t) p (fun v => compute (gridInput p v)) df)
      (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J) (7+ε) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀Of (t := t) p (fun v => compute (gridInput p v)) df w‖ ≤ 1 := by
  let Jn := ((2 : ℂ)^j)⁻¹ • J
  have hnorm : ‖Jn‖ ≤ 1 := by
    dsimp only [Jn]
    rw [norm_smul,norm_inv,norm_pow,RCLike.norm_two]
    apply (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2^j)).mpr
    simpa only [mul_one] using hJn.trans hj
  have hquant (v : ZMod s → ℂ) :
      ‖Jn ((1/2 : ℂ) • fun i => value p (gridInput p v i))-Jn ((1/2 : ℂ) • v)‖ ≤ 1/(2 : ℝ)^p := by
    rw [←map_sub,←smul_sub]
    calc
      _ ≤ ‖Jn‖*‖(1/2 : ℂ) • ((fun i => value p (gridInput p v i))-v)‖ := le_opNorm _ _
      _ ≤ 1*((1/2)* (2/(2 : ℝ)^p)) := by
        have hhalf : ‖(1/2 : ℂ) • ((fun i => value p (gridInput p v i))-v)‖ ≤ (1/2)*(2/(2 : ℝ)^p) := by
          rw [norm_smul]
          have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
          rw [hn]
          exact mul_le_mul_of_nonneg_left (gridInput_error p v) (by norm_num)
        exact mul_le_mul hnorm hhalf (norm_nonneg _) zero_le_one
      _ = 1/(2 : ℝ)^p := by ring
  have hspec := resampB₀Of_spec (t := t) (α := α) (p := p)
    (J := Jn) (εJ := ε+1) (fun v => compute (gridInput p v)) df (fun v hv => by
      have hF : ∀ i, ‖value p (gridInput p v i)‖ ≤ 1 := fun i =>
        (norm_le_pi_norm (fun i => value p (gridInput p v i)) i).trans ((gridInput_norm p v).trans hv)
      obtain ⟨hunit,herror⟩ := hgrid (gridInput p v) hF
      refine ⟨hunit,?_⟩
      have hsplit := mul_le_mul_of_nonneg_left
        (norm_sub_le_norm_sub_add_norm_sub (compute (gridInput p v))
          (Jn ((1/2 : ℂ) • fun i => value p (gridInput p v i))) (Jn ((1/2 : ℂ) • v)))
        (by positivity : (0 : ℝ) ≤ 2^p)
      have hq := mul_le_mul_of_nonneg_left (hquant v) (by positivity : (0 : ℝ) ≤ 2^p)
      have hcancel : (2 : ℝ)^p*(1/(2 : ℝ)^p) = 1 := by field_simp
      rw [hcancel] at hq
      nlinarith only [hsplit,herror,hq]) hdf hdf1
  simpa only [Jn,resampB₀_smul,show 6+(ε+1) = 7+ε by ring] using hspec

end IntegerMultBounds.MathlibTM2.Mult.FastB0
