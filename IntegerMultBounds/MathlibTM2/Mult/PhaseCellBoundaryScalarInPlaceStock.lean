module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScalarInPlace
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandScaleStock

/-! In-place boundary scaling shares the scalar-stream reserve.
Both order-restoring moves preserve storage throughout their execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem boundaryScalarInPlaceP_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (port : RsbR) (hfree : RsbFree port .dtab .ya)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs : List GaussianInt) (c : ℤ) (hxs : ∀ z ∈ xs, Fits w z)
    (hc : Fits w (⟨c,0⟩ : GaussianInt))
    (v : HS T Q A U) (S : Stacks T A) (hclean : RsbClean ι S)
    (hr : RsbReady (fun r => S.R (rg r)) w q)
    (hx : S.R (rg port) = cstream A w xs)
    (hy : S.R (rg .dtab) = csyms A w (⟨c,0⟩ : GaussianInt)) (ho : S.R (rg .ya) = [])
    {n : ℕ} {z : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (boundaryScalarInPlaceP rg hι hT hQ port) (mk v S) n z)
    (C : ℕ) (hpush : mnProgPush (cmulBlock (rsbCr rg port .dtab .ya)
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ
        (rsbCr rg port .dtab .ya))) ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤
      mnSize (mk v S)+depth+realScalarWorkspace C w xs.length) depth
      (boundaryScalarInPlaceP rg hι hT hQ port) (mk v S) n z := by
  obtain ⟨v₁,n₁,_,_,hscale⟩ := bandScaleP_exec_within (body := body)
    hrg hdisj hι hT hQ hA hfree hw hq xs c hxs hc v S hclean hr hx hy ho
  have hs := hscale C hpush depth
  cases he with
  | seq he₁ he₂ =>
    obtain ⟨hn,hz⟩ := hs.toExec.unique he₁
    subst hn
    subst hz
    cases he₂ with
    | seq hm₁ hm₂ =>
      have hm₁' := moveR_within _ _ _ hm₁ depth _ hs.final
      exact .seq hs (.seq hm₁' (moveR_within _ _ _ hm₂ depth _ hm₁'.final))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
