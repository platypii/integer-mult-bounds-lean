module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions

/-! Derive normalization magnitude from unit inputs and principal-system stability. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Both real solves use half the original unit input. Their shared dominance
margin bounds the assembled complex target independently of halo length. -/
theorem componentSolution_stable_bound {s : ℕ} (p q : ℕ) (hp : 0 < p) (hpq : p+1 ≤ q)
    (M : Matrix (ZMod s) (ZMod s) ℝ) (active : Finset (ZMod s))
    (hdom : SchurDominance.DominatesOn M active (1/(8*(p : ℝ))))
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M active (y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) :
    ∀ F ∈ Fs, ∀ i ∈ active, ‖componentSolution y F i‖ ≤ 8*(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcomponents := complexComponentFields_norm_le p Fs hF
  have hscalar : ∀ F ∈ complexComponentFields Fs, ∀ i ∈ active, |y F i| ≤ 4*(p : ℝ) := by
    intro F hmem i hi
    have hb : ∀ j ∈ active, |(value q ((2 : GaussianInt)^(q-p-1)*F j)).re| ≤ (1/2 : ℝ) := by
      intro j hj
      have hunit := hcomponents F hmem j
      rw [(packedInputShift_value_fits p q hpq (F j) hunit).1]
      calc
        _ ≤ ‖(1/2 : ℂ)*value p (F j)‖ := Complex.abs_re_le_norm _
        _ = (1/2 : ℝ)*‖value p (F j)‖ := by rw [norm_mul]; norm_num
        _ ≤ 1/2 := by linarith
    have h := SchurDominance.solves_bound M active (1/(8*(p : ℝ))) (by positivity)
      hdom (y F) _ (hy F hmem) (1/2) hb i hi
    have hquot : (1/2 : ℝ)/(1/(8*(p : ℝ))) = 4*(p : ℝ) := by field_simp; ring
    simpa only [hquot] using h
  intro F hmem i hi
  have hre := hscalar (fun j => realPartWord (F j))
    (List.mem_append_left _ (List.mem_map.mpr ⟨F,hmem,rfl⟩)) i hi
  have him := hscalar (fun j => imagPartWord (F j))
    (List.mem_append_right _ (List.mem_map.mpr ⟨F,hmem,rfl⟩)) i hi
  calc
    _ ≤ 2*(4*(p : ℝ)) := componentSolution_norm_le y F i _ hre him
    _ = _ := by ring

/-- The rounding allowance follows from stability, rather than an additional
magnitude witness about the numerical target. -/
theorem componentSolution_round_magnitude {s : ℕ} (p : ℕ)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (F : ZMod s → GaussianInt) (i : ZMod s)
    (hbound : ‖componentSolution y F i‖ ≤ 8*(p : ℝ)) :
    ‖componentSolution y F i‖ ≤ 4*(2 : ℝ)^(p+8) := by
  have hp : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
  have hpow : (2 : ℝ)^(p+8) = 256*(2 : ℝ)^p := by rw [pow_add]; norm_num; ring
  rw [hpow]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
