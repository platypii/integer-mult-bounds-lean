module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineDriver

/-! Apply a retained real scalar to a bank port and restore natural word order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def boundaryScalarInPlaceP (rg : RsbR → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (port : RsbR) : Pr P T Q A U :=
  .seq (bandScaleP rg hι hT hQ port .dtab .ya)
    (.seq (moveR (rg .ya) (rg .ac2) id) (moveR (rg .ac2) (rg port) id))

def boundaryScalarInPlaceCost (w N : ℕ) : ℕ := N*(rmulCost w+12*w+8)+12

theorem boundary_scalarInPlace_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (port : RsbR) (hfree : RsbFree port .dtab .ya) (hac : port ≠ .ac2)
    (w q : ℕ) (σ : RsbR → List (Fin (A+4))) (hready : RsbReady σ w q)
    (hw : 1 ≤ w) (hq : q ≤ w) (xs : List GaussianInt) (c : ℤ)
    (hxs : ∀ z ∈ xs, Fits w z) (hc : Fits w (⟨c,0⟩ : GaussianInt))
    (hsrc : σ port = cstream A w xs) (hscalar : σ .dtab = csyms A w (⟨c,0⟩ : GaussianInt))
    (hya : σ .ya = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (boundaryScalarInPlaceP rg hι hT hQ port) σ
      (Function.update σ port (cstream A w (xs.map fun z => tdivN q (z * ⟨c,0⟩))))
      (boundaryScalarInPlaceCost w xs.length) := by
  have hsy := hfree.2.1
  have hscale := band_scale_runs (body := body) hrg hdisj hι hT hQ hA hfree
    σ hready hw hq xs c hxs hc hsrc hscalar hya
  let σ₁ := Function.update (Function.update σ .ya
    (cstream A w (xs.map fun z => tdivN q (z * ⟨c,0⟩)))) port []
  have hmove₁ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ya) (b := .ac2) (by decide) σ₁
  let σ₂ := Function.update (Function.update σ₁ .ya []) .ac2 ((σ₁ .ya).reverse ++ σ₁ .ac2)
  have hmove₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := port) hac.symm σ₂
  refine ((RsbRuns.seq hdisj hscale (RsbRuns.seq hdisj hmove₁ hmove₂)).congr ?_).mono ?_
  · funext r
    by_cases hs : r = port
    · subst r
      simp [σ₂,σ₁,hsy,hsy.symm,hac,hac.symm,hac2]
    by_cases hy : r = .ya
    · subst r
      simp [σ₂,σ₁,hsy,hsy.symm,hac,hac.symm,hya,hac2]
    by_cases ha : r = .ac2
    · subst r
      simp [σ₂,σ₁,hsy,hsy.symm,hac,hac.symm,hac2]
    simp [σ₂,σ₁,hs,hy,ha,hsy,hsy.symm,hac,hac.symm]
  · simp [boundaryScalarInPlaceCost,σ₂,σ₁,hac.symm,hsy.symm,hac2,length_cstream,Nat.mul_add]
    ring_nf; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
