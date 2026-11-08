module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRealRoundAccuracy

/-! Real scalar rows incur one rounding coordinate, not the generic complex
allowance. Pairing two such rows recovers the published complex budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine

theorem norm_rhoC_sub_real (p : ℕ) (z : ℂ) (hz : z.im = 0) :
    ‖rhoC p z-z‖ ≤ 1/(2 : ℝ)^p := by
  have hzero : rho0 0 = 0 := by simp [rho0]
  have hr : rhoC p z-z = (((rho0 ((2 : ℝ)^p*z.re) : ℝ)/(2 : ℝ)^p-z.re : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,rhoC_re,rhoC_im,Complex.ofReal_re,
        Complex.ofReal_im,hz,mul_zero,hzero,Int.cast_zero,zero_div,sub_self]
  rw [hr,Complex.norm_real,Real.norm_eq_abs]
  have hp : (0 : ℝ) < 2^p := by positivity
  have heq : (rho0 ((2 : ℝ)^p*z.re) : ℝ)/(2 : ℝ)^p-z.re =
      ((rho0 ((2 : ℝ)^p*z.re) : ℝ)-(2 : ℝ)^p*z.re)/(2 : ℝ)^p := by field_simp
  rw [heq,abs_div,abs_of_pos hp]
  exact (div_lt_div_of_pos_right (abs_rho0_sub_lt _) hp).le

theorem scaleRound_real_error (p j : ℕ) (y x : ℂ) (hy : y.im = 0)
    (e : ℝ) (he : ‖y-x‖ ≤ e) :
    ‖rhoC p (((2 : ℂ)^j)⁻¹*y)-((2 : ℂ)^j)⁻¹*x‖ ≤ 1/(2 : ℝ)^p+e/(2 : ℝ)^j := by
  have hscaled : (((2 : ℂ)^j)⁻¹*y).im = 0 := by
    have hpow : ((2 : ℂ)^j).im = 0 := by
      have hc : (2 : ℂ)^j = ((2 : ℝ)^j : ℝ) := by norm_cast
      rw [hc]
      rfl
    simp only [Complex.mul_im,Complex.inv_im,hpow,hy,neg_zero,zero_div,mul_zero,zero_mul,add_zero]
  have hd : ‖((2 : ℂ)^j)⁻¹*y-((2 : ℂ)^j)⁻¹*x‖ ≤ e/(2 : ℝ)^j := by
    rw [←mul_sub,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2^j))
  calc
    _ = ‖(rhoC p (((2 : ℂ)^j)⁻¹*y)-((2 : ℂ)^j)⁻¹*y)+
        (((2 : ℂ)^j)⁻¹*y-((2 : ℂ)^j)⁻¹*x)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_rhoC_sub_real p _ hscaled) hd

theorem packedRealFinalRound_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a L : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (D : ZMod s → GaussianInt) (hreal : ∀ i, (D i).im = 0) (hfits : ∀ i, Fits w (D i))
    (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (x : ZMod s → ℝ) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^E) (tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn active (fun i => (value q (D i)).re) x e) :
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p k a
        (cstream A k (packedInterval a L (fun i => finalRoundWord w q p j (D i)))++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) (1/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  have hread := packedRealRead_accuracy hA q w a L hw D hreal hfits active hfit hactive x e [] herror
  intro i hi
  have hx' : ‖(x i : ℂ)‖ ≤ 4*(2 : ℝ)^E := by simpa only [Complex.norm_real] using hx i hi
  have hnorm := computed_solution_norm_of_error E _ (x i : ℂ) e he hx' (hread i hi)
  rw [packedIntervalRead_finalRound hA p q j w k E a L hp hw hk D tail [] hfit i
    (hactive i hi).1 (hactive i hi).2 hnorm]
  apply scaleRound_real_error p j _ _ ?_ e (hread i hi)
  rw [packedIntervalRead_decode q w a L D [] hfit i (hactive i hi).1 (hactive i hi).2,
    decodeWord_of_fits hA hw (D i) (hfits i)]
  simp only [value,hreal i,Int.cast_zero,zero_div]

theorem packedRealFinalRoundBatch_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a L : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ x ∈ xs, ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^E)
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits w (D i))
    (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
      (fun i => (value q (D i)).re) x e) xs Ds) :
    List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead p k a (cstream A k (packedInterval a L D)++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) (1/(2 : ℝ)^p+e/(2 : ℝ)^j))
      xs (Ds.map (fun D i => finalRoundWord w q p j (D i))) := by
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_of_length_eq_of_get hgood.length_eq
  intro i hi hj
  exact packedRealFinalRound_accuracy hA p q j w k E a L hp hw hk (Ds.get ⟨i,hj⟩)
    (hreal _ (List.get_mem _ _)) (hfits _ (List.get_mem _ _)) active hfit hactive
    (xs.get ⟨i,hi⟩) e he (hx _ (List.get_mem _ _)) tail (hgood.get hi hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
