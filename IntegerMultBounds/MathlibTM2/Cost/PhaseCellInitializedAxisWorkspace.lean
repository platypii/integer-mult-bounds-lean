module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreExposureTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellStreamedDyadicBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisCleanupBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundaryArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchPush
import Mathlib.Tactic.Linarith

/-! The complete ordinary axis reserve is linear replica traffic plus one
shared volume allowance. All coefficients belong to fixed closed programs. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

private theorem axisWorkspace_le (N s t p W total cW init gather callback publication seam boundary crop C : ℕ)
    (hst : s ≤ t) (hW : W ≤ cW*p) (htotal : 1 ≤ total) :
    init*(N*(s*W))+
      (((gather*(N*s*W)+callback*N*t*p+47*total)+
        (2*total+publication*(N*s*W)+12)+
        ((seam*(N*s*p)+2*(C+1)*total+86)+(boundary*(N*(s*W))+13*(crop*(N*(s*W)))))+
        3*(21*(N*(s*W))+12))) ≤
    (callback+cW*(init+gather+publication+boundary+13*crop+63)+seam)*N*t*p+
      (183+2*(C+1))*total := by
  have htraffic : N*(s*W) ≤ cW*(N*t*p) := by
    have hh := Nat.mul_le_mul_left N (Nat.mul_le_mul hst hW)
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have hseam : N*s*p ≤ N*t*p := Nat.mul_le_mul_right p (Nat.mul_le_mul_left N hst)
  have hbank := Nat.mul_le_mul_left (init+gather+publication+boundary+13*crop+63) htraffic
  have hs := Nat.mul_le_mul_left seam hseam
  have hc := Nat.mul_le_mul_left 134 htotal
  nlinarith only [hbank,hs,hc]

noncomputable def initializedAxisWorkspaceTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct cW cV cG cVPub cDB : ℕ) : ℕ :=
  let C := gridDispatchPush (A := A) (U := U) hR hQ
  fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW+
    cW*(560+100*cV+(3*coreExposureTrafficFactor cG cW+12+
      12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))+
      (4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))+
      boundaryHeaderTrafficFactor cDB+13*boundaryPublicationTrafficFactor cDB+63)+
    ((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)

noncomputable def initializedAxisWorkspaceVolumeFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : ℕ :=
  183+2*(gridDispatchPush (A := A) (U := U) hR hQ+1)

theorem initializedAxisWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct cW cV cG cVPub cDB N s t p W total : ℕ) (hst : s ≤ t) (hW : W ≤ cW*p) (htotal : 1 ≤ total) :
    let C := gridDispatchPush (A := A) (U := U) hR hQ
    let seamStock := (((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(N*s*p)+2*(C+1)*total+86)+
      (boundaryHeaderTrafficFactor cDB*(N*(s*W))+13*(boundaryPublicationTrafficFactor cDB*(N*(s*W))))
    (560+100*cV)*(N*(s*W))+
      (((3*coreExposureTrafficFactor cG cW+12+
        12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(N*s*W)+
        fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*N*t*p+47*total)+
        (2*total+(4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(N*s*W)+12)+
        seamStock+3*(21*(N*(s*W))+12)) ≤
    initializedAxisWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW cV cG cVPub cDB*N*t*p+
      initializedAxisWorkspaceVolumeFactor (A := A) (U := U) hR hQ*total := by
  exact axisWorkspace_le N s t p W total cW (560+100*cV)
    (3*coreExposureTrafficFactor cG cW+12+12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))
    (fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW)
    (4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))
    ((gridDispatchPush (A := A) (U := U) hR hQ+1)*((1312000+756)*(1032+8*ct)+504)+1440)
    (boundaryHeaderTrafficFactor cDB) (boundaryPublicationTrafficFactor cDB)
    (gridDispatchPush (A := A) (U := U) hR hQ) hst hW htotal

end IntegerMultBounds.MathlibTM2.Cost
