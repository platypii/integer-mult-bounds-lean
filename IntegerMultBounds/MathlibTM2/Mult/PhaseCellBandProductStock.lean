module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineDriver
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStreamStock

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

theorem rsb_rmulStream_exec_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (hxs : ∀ z ∈ xs, Fits w z) (hys : ∀ z ∈ ys, Fits w z ∧ z.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : RsbClean ι S)
    (hr : RsbReady (fun r => S.R (rg r)) w q)
    (hx : S.R (rg x) = cstream A w xs) (hy : S.R (rg y) = cstream A w ys) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(rmulCost w+6*w+2)+8 ∧
      ∀ C, mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
        ι hι hT hQ (rsbCr rg x y o)) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v S)+depth+realWeightWorkspace C w xs.length) depth
        (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) (mk v S) n
        (mk v' {S with R := (Function.update S.R (rg o)
          (cstream A w (List.zipWith (fun a b => tdivN q (a*b)) xs ys)++S.R (rg o)))}) := by
  exact realWeightStream_exec_of_fits_within (body := body)
    (hrg.comp (rsbRemap_injective hfree)) (fun r j => hdisj (rsbRemap x y o r) j)
    hι hT hQ hA hw hq xs ys hlen hxs hys v S
    (fun j => ⟨hclean.1 (ι j),hclean.2 j⟩) (hr.ready x y o) hx hy
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

/-- Attach the shared reserve to an existing band-product trace. -/
theorem rsb_rmulStream_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (hxs : ∀ z ∈ xs, Fits w z) (hys : ∀ z ∈ ys, Fits w z ∧ z.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hclean : RsbClean ι S)
    (hr : RsbReady (fun r => S.R (rg r)) w q)
    (hx : S.R (rg x) = cstream A w xs) (hy : S.R (rg y) = cstream A w ys)
    {n : ℕ} {z : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (cmulStream (rsbCr rg x y o)
      (rmulOne ι hι hT hQ (rsbCr rg x y o))) (mk v S) n z)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤
      mnSize (mk v S)+depth+realWeightWorkspace C w xs.length) depth
      (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) (mk v S) n z := by
  obtain ⟨v',m,_,_,hb⟩ := rsb_rmulStream_exec_within (body := body)
    hrg hdisj hι hT hQ hA hfree hw hq xs ys hlen hxs hys v S hclean hr hx hy
  have ht := hb C hpush depth
  obtain ⟨hn,hz⟩ := ht.toExec.unique he
  rw [hn,hz] at ht
  exact ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
