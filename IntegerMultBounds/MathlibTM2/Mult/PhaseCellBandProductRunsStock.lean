module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandProductStock

/-! Banded column and reciprocal products reuse the varying-real-factor
stream bound through an arbitrary injective role map. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_rmulStream_runs_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w q : ℕ}
    (ρ : RsbR → List (Fin (A+4))) (hr : RsbReady ρ w q) (hw : 1 ≤ w) (hq : q ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (hxs : ∀ z ∈ xs, Fits w z) (hys : ∀ z ∈ ys, Fits w z ∧ z.im = 0)
    (hx : ρ x = cstream A w xs) (hy : ρ y = cstream A w ys)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) ρ
      (Function.update ρ o (cstream A w (List.zipWith (fun a b => tdivN q (a*b)) xs ys)++ρ o))
      (xs.length*(rmulCost w+6*w+2)+8) (realWeightWorkspace C w xs.length) := by
  have hrun := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA hfree
    hr hw hq xs ys hlen hxs hys hx hy
  intro v S hc hS
  obtain ⟨v',F,n,hu,hn,he,hh,hf⟩ := hrun v S hc hS
  refine ⟨v',F,n,hu,hn,hh,hf,?_⟩
  intro depth
  have hρ : (fun r => S.R (rg r)) = ρ := funext hS
  exact rsb_rmulStream_within hrg hdisj hι hT hQ hA hfree hw hq xs ys hlen hxs hys
    v S hc (by rw [hρ]; exact hr) ((hS x).trans hx) ((hS y).trans hy) he C hpush depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
