module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryAxisWorkspace
import Mathlib.Tactic.Ring

/-! Factor preparation separates banded storage from a single arithmetic reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {ι : Fin 64 → Fin T}

theorem bandAxisPrepWorkspace_le (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (w k K n J L : ℕ) :
    let C := bandNewtonStepPush (P := P) (A := A) (U := U) rg hι hT hQ
    bandAxisPrepWorkspace (P := P) (A := A) (U := U) rg hι hT hQ w k K n J L ≤
      10000*(C+J+L+1)*(n+k+2)*(k+2)*(w+1)+
        2*(C+J+L+1)*rmulCost w+4*K := by
  dsimp only
  unfold bandAxisPrepWorkspace realWeightWorkspace bandNewtonStepCost bandAxisOrgCost bandTStepCost
  ring_nf
  omega

theorem boundaryAxisPrepWorkspace_le (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (w k K n : ℕ) :
    let C := bandNewtonStepPush (P := P) (A := A) (U := U) rg hι hT hQ
    let J := factorRmulPush (P := P) (A := A) (U := U) (rsbCr rg .hv .xa .hc) hι hT hQ
    let L := factorRmulPush (P := P) (A := A) (U := U) (rsbCr rg .ya .xs .pr) hι hT hQ
    boundaryAxisPrepWorkspace (P := P) (A := A) (U := U) rg hι hT hQ w k K n ≤
      10000*(C+J+L+1)*(n+k+2)*(k+2)*(w+1)+
        2*(C+J+L+1)*rmulCost w+4*K := by
  unfold boundaryAxisPrepWorkspace
  exact bandAxisPrepWorkspace_le rg hι hT hQ w k K n _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
