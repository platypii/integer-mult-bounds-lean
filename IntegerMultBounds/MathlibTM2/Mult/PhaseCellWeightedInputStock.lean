module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStreamStock

/-! Constructed reciprocal weights and the normalization shift retain the
complete pointwise stream's shared numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

theorem weightedInputStream_exec_within
    (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w cExp e : ℕ} (hw : q + (cExp + e) + 2 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = ds.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ cExp)
    (hds : ∀ d ∈ ds, 1 / (2 : ℝ) ^ e ≤ (d : ℝ))
    (v : HS T Q A U) (S : Stacks T A) (hclean : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w (q + (cExp + e + 1)))
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w (reciprocalWeightWords q ds))
    (hxsv : S.R (cr .xsv) = []) (hysv : S.R (cr .ysv) = []) (hacc : S.R (cr .acc) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      ∀ C, mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realWeightWorkspace C w xs.length)
        depth (realWeightStream cr ι hι hT hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w (weightedInputNumerators q cExp e xs ds) ++ S.R (cr .out))) }) := by
  exact realWeightStream_exec_within (body := body) hcr hdisj hι hT hQ hA hw (by omega)
    xs (reciprocalWeightWords q ds) (by simp [reciprocalWeightWords, hlen]) hxs
    (reciprocalWeightWords_norm ds hds) v S hclean hr hx hy hxsv hysv hacc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
