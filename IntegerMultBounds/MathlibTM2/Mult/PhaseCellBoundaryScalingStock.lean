module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizeRuns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscaleRuns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScalarInPlaceStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock

/-! Both boundary scale directions share the in-place scalar workspace rule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.BandFactor
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem boundary_scalarInPlace_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (port : RsbR) (hfree : RsbFree port .dtab .ya) (hac : port ≠ .ac2)
    (w q : ℕ) (σ : RsbR → List (Fin (A+4))) (hready : RsbReady σ w q)
    (hw : 1 ≤ w) (hq : q ≤ w) (xs : List GaussianInt) (c : ℤ)
    (hxs : ∀ z ∈ xs, Fits w z) (hc : Fits w (⟨c,0⟩ : GaussianInt))
    (hsrc : σ port = cstream A w xs) (hscalar : σ .dtab = csyms A w (⟨c,0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = [])
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr rg port .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ (rsbCr rg port .dtab .ya))) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (boundaryScalarInPlaceP rg hι hT hQ port) σ
      (Function.update σ port (cstream A w (xs.map fun z => tdivN q (z * ⟨c,0⟩))))
      (boundaryScalarInPlaceCost w xs.length) (realScalarWorkspace C w xs.length) := by
  have hrun := boundary_scalarInPlace_runs (body := body) hrg hdisj hι hT hQ hA port hfree hac
    w q σ hready hw hq xs c hxs hc hsrc hscalar hya hac2
  intro v S hclean hS
  obtain ⟨v',F,n,hu,hn,he,hh,hf⟩ := hrun v S hclean hS
  refine ⟨v',F,n,hu,hn,hh,hf,?_⟩
  intro depth
  have hσ : (fun r => S.R (rg r)) = σ := funext hS
  exact boundaryScalarInPlaceP_within hrg hdisj hι hT hQ hA port hfree hw hq xs c hxs hc
    v S hclean (by rw [hσ]; exact hready) ((hS port).trans hsrc) ((hS .dtab).trans hscalar)
    ((hS .ya).trans hya) he C hpush depth

theorem boundary_normalize_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q E e : ℕ) (hq : q = E+e+1) (σ : RsbR → List (Fin (A+4)))
    (hready : RsbReady σ (2*q+8) q) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E)
    (hx : σ .vk = cstream A (2*q+8) xs)
    (hc : σ .dtab = csyms A (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = [])
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr rg .vk .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ (rsbCr rg .vk .dtab .ya))) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (boundaryNormalizeP rg hι hT hQ) σ
      (Function.update σ .vk (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))))
      (boundaryNormalizeCost (2*q+8) xs.length) (realScalarWorkspace C (2*q+8) xs.length) := by
  have hfx : ∀ z ∈ xs, Fits (2*q+8) z := fun z hz => (boundary_normalization_fits q E e hq z (hbound z hz)).1
  have hz0 : |gv q (0 : ℤ)| ≤ (2 : ℝ)^E := by rw [gv_zero,abs_zero]; positivity
  have hfc : Fits (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt) :=
    (boundary_normalization_fits q E e hq 0 ⟨hz0,hz0⟩).2.1
  have hrun := boundary_scalarInPlace_runs_within (body := body) hrg hdisj hι hT hQ hA .vk
    ⟨by decide,by decide,by decide,fun _ => ⟨by simp,by simp,by simp⟩⟩ (by decide)
    (2*q+8) q σ hready (by omega) (by omega) xs ((2 : ℤ)^e) hfx hfc hx hc hya hac2 C hpush
  have heq : (xs.map fun z => tdivN q (z * ⟨(2 : ℤ)^e,0⟩)) = xs.map (normalizeBoundaryWord q e) :=
    List.map_congr_left (fun _ _ => rfl)
  change RsbRunsWithin (body := body) (rg := rg) (ι := ι) (boundaryScalarInPlaceP rg hι hT hQ .vk) σ
    (Function.update σ .vk (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))))
    (boundaryScalarInPlaceCost (2*q+8) xs.length) (realScalarWorkspace C (2*q+8) xs.length)
  simpa only [heq] using hrun

theorem boundary_unscale_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (σ : RsbR → List (Fin (A+4)))
    (hready : RsbReady σ (2*q+8) q) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (hx : σ .dout = cstream A (2*q+8) xs)
    (hc : σ .dtab = csyms A (2*q+8) (⟨(2 : ℤ)^(q+q/2+1),0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = [])
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr rg .dout .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ (rsbCr rg .dout .dtab .ya))) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (boundaryUnscaleP rg hι hT hQ) σ
      (Function.update σ .dout (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))))
      (boundaryScalarInPlaceCost (2*q+8) xs.length) (realScalarWorkspace C (2*q+8) xs.length) := by
  have hxs : ∀ z ∈ xs, Fits (2*q+8) z := fun z hz => (boundary_unscale_fits q p hpq z (hbound z hz)).1
  have hrun := boundary_scalarInPlace_runs_within (body := body) hrg hdisj hι hT hQ hA .dout
    ⟨by decide,by decide,by decide,fun _ => ⟨by simp,by simp,by simp⟩⟩ (by decide)
    (2*q+8) q σ hready (by omega) (by omega) xs ((2 : ℤ)^(q+q/2+1)) hxs
    (boundary_unscale_scalar_fits q) hx hc hya hac2 C hpush
  have heq : (xs.map fun z => tdivN q (z * ⟨(2 : ℤ)^(q+q/2+1),0⟩)) = xs.map (unscaleBoundaryWord q) :=
    List.map_congr_left (fun z _ => boundary_unscale_product q z)
  simpa only [boundaryUnscaleP,heq] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
