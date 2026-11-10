module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCleanArchiveWidthSetup

/-! The selector's produced rows and borrowed width generate the numerical
payload count. No count of the encoded archive is supplied or computed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

theorem count_regs : [aux 7,geometry 116,geometry 94,aux 6,aux 2,aux 3,aux 4].Nodup := by
  simp [aux,geometry,selector,port_injective.eq_iff,LocalRecoveryLayout.geometry,
    LocalRecoveryLayout.port_injective.eq_iff]

def prepareCount : Pr P tapes Q A U :=
  cleanArchiveWidthSetup (aux 7) (geometry 116) (geometry 94) (aux 6) (aux 2) (aux 3) (aux 4)

theorem prepareCount_exec (N rows W depth : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hN : (S.R (aux 7)).length = N) (hrows : (S.R caller.span).length = rows)
    (hW : (S.R (caller.controls 0)).length = W)
    (hblank : ∀ i ∈ [aux 6,caller.count,caller.saved,caller.tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ archiveWidthSetupCost N rows W+2*(rows*W)+3 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*archiveWidthSetupCost N rows W) depth prepareCount (mk v S) n
        (mk v' {S with R := Function.update S.R caller.count (List.replicate (N*(rows*W)) tick)}) := by
  exact cleanArchiveWidthSetup_exec body (aux 7) (geometry 116) (geometry 94) (aux 6) (aux 2)
    (aux 3) (aux 4) count_regs N rows W depth v S hN hrows hW hblank

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
