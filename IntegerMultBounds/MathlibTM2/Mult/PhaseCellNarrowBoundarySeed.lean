module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Generate the count metadata's binary word-width input from its unary ruler.
The retained ruler and arithmetic width survive literally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A : ℕ} {P U : Type}

def narrowBoundarySeed : Pr P 117 Q A U := toBinary 17 58 57 27 28 29

theorem narrowBoundarySeed_exec_within (body : P → Pr P 117 Q A U) (D w : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hword : (S.R 17).length = w) (hwidth : (S.R 58).length = D)
    (hblank : S.R 57 = []) (hsaved : S.R 27 = []) (htmp : S.R 28 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ w*(4*D+10)+4*D+8 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*D+4)) depth
        narrowBoundarySeed (mk v S) n
        (mk v' {S with R := Function.update S.R 57 (binSyms D w)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := toBinary_exec_within (body := body)
    (u := 17) (wR := 58) (c := 57) (saved := 27) (tmp := 28)
    (by decide +kernel) 29 v S hblank hsaved htmp depth
  refine ⟨v',n,hu,?_,?_⟩
  · simpa only [hword,hwidth] using hn
  · simpa only [narrowBoundarySeed,hword,hwidth] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
