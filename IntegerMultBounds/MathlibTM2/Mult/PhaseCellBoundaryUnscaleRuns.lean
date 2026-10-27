module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScalarInPlace

/-! Execute exact unscaling of the triangular solution without changing the factor tables. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def boundaryUnscaleP (rg : RsbR → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  boundaryScalarInPlaceP rg hι hT hQ .dout

theorem boundary_unscale_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (σ : RsbR → List (Fin (A+4)))
    (hready : RsbReady σ (2*q+8) q) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (hx : σ .dout = cstream A (2*q+8) xs)
    (hc : σ .dtab = csyms A (2*q+8) (⟨(2 : ℤ)^(q+q/2+1),0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (boundaryUnscaleP rg hι hT hQ) σ
      (Function.update σ .dout (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q))))
      (boundaryScalarInPlaceCost (2*q+8) xs.length) := by
  have hxs : ∀ z ∈ xs, Fits (2*q+8) z := fun z hz => (boundary_unscale_fits q p hpq z (hbound z hz)).1
  have hrun := boundary_scalarInPlace_runs (body := body) hrg hdisj hι hT hQ hA .dout
    ⟨by decide,by decide,by decide,fun _ => ⟨by simp,by simp,by simp⟩⟩ (by decide)
    (2*q+8) q σ hready (by omega) (by omega) xs ((2 : ℤ)^(q+q/2+1)) hxs
    (boundary_unscale_scalar_fits q) hx hc hya hac2
  have heq : (xs.map fun z => tdivN q (z * ⟨(2 : ℤ)^(q+q/2+1),0⟩)) = xs.map (unscaleBoundaryWord q) :=
    List.map_congr_left (fun z _ => boundary_unscale_product q z)
  simpa only [boundaryUnscaleP,heq] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
