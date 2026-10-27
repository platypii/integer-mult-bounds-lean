module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalization

/-! Normalize a gathered RHS in place while preserving the triangular factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def boundaryNormalizeP (rg : RsbR → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (bandScaleP rg hι hT hQ .vk .dtab .ya)
    (.seq (moveR (rg .ya) (rg .ac2) id) (moveR (rg .ac2) (rg .vk) id))

def boundaryNormalizeCost (w N : ℕ) : ℕ := N*(rmulCost w+12*w+8)+12

theorem boundary_normalize_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q E e : ℕ) (hq : q = E+e+1) (σ : RsbR → List (Fin (A+4)))
    (hready : RsbReady σ (2*q+8) q) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E)
    (hx : σ .vk = cstream A (2*q+8) xs)
    (hc : σ .dtab = csyms A (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (boundaryNormalizeP rg hι hT hQ) σ
      (Function.update σ .vk (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))))
      (boundaryNormalizeCost (2*q+8) xs.length) := by
  have hfx : ∀ z ∈ xs, Fits (2*q+8) z := fun z hz => (boundary_normalization_fits q E e hq z (hbound z hz)).1
  have hz0 : |gv q (0 : ℤ)| ≤ (2 : ℝ)^E := by rw [gv_zero,abs_zero]; positivity
  have hfc : Fits (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt) :=
    (boundary_normalization_fits q E e hq 0 ⟨hz0,hz0⟩).2.1
  have hscale := band_scale_runs (body := body) hrg hdisj hι hT hQ hA
    (x := .vk) (y := .dtab) (o := .ya)
    ⟨by decide,by decide,by decide,fun _ => ⟨by simp,by simp,by simp⟩⟩
    σ hready (by omega) (by omega) xs ((2 : ℤ)^e) hfx hfc hx hc hya
  let σ₁ := Function.update (Function.update σ .ya
    (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e)))) .vk []
  have hmove₁ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ya) (b := .ac2) (by decide) σ₁
  let σ₂ := Function.update (Function.update σ₁ .ya []) .ac2 ((σ₁ .ya).reverse ++ σ₁ .ac2)
  have hmove₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₂
  refine ((RsbRuns.seq hdisj hscale (RsbRuns.seq hdisj hmove₁ hmove₂)).congr ?_).mono ?_
  · funext r
    cases r <;> simp [σ₂,σ₁,hya,hac2]
  · simp [boundaryNormalizeCost,σ₂,σ₁,hac2,length_cstream,Nat.mul_add]
    ring_nf; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
