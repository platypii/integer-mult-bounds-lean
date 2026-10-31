module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStock
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! One scalar-table iteration restores its scalar word before the next input
coefficient. Its numerical reserve depends on word width, not stream length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

theorem cmulBlock_rmulOne_noCalls (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) :
    WordCmd.NoCalls (cmulBlock cr (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr)) := by
  simp [cmulBlock,cwhileP,rmulOne_noCalls,moveR,whileR,WordCmd.NoCalls]

theorem rmulBlock_one_exec_within (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A+4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    {x y : GaussianInt} (hx : Fits w x) (hy : Fits w y) (hre : y.im = 0)
    {rx : List (Fin (A+4))} (hxs : ρ .xs = csyms A w x++rx)
    (hys : ρ .ys = csyms A w y) (hysv : ρ .ysv = [])
    (C : ℕ) (hpush : mnProgPush (cmulBlock cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr)) ≤ C)
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ rmulCost w+2*w+6 ∧
      CHolds cr S' (blockSt ρ w (fun x y => tdivN p (x*y)) rx [(x,y)]) ∧ CFr cr S S' ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v S)+depth+C*(rmulCost w+2*w+6))
        depth (cmulBlock cr (rmulOne ι hι hT hQ cr)) (mk v S) n (mk v' S') := by
  have hb : CRuns body cr ι (cmulBlock cr (rmulOne ι hι hT hQ cr)) ρ
      (blockSt ρ w (fun x y => tdivN p (x*y)) rx [(x,y)]) (rmulCost w+2*w+6) := by
    simpa using block_runs hcr hdisj (rmulOne_spec hcr hdisj hι hT hQ hA hw hp) hw hr [(x,y)]
      (by simp [hx,hy,hre]) (by simpa using hxs) (by simpa using hys) hysv
  exact hb.exec_within_native
    (WordCmd.native_of_noCalls (cmulBlock_rmulOne_noCalls hι hT hQ) hpush) v S hc hS

end IntegerMultBounds.MathlibTM2.Fast
