module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloGroupPreparationStock
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Halo geometry construction separates its shared table from encoded metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem conditionalHaloGroupPreparationWorkspace_le_volume
    (P N q l s t u band a b L : ℕ) :
    let V := haloGeometryWidth t (2*q+8)
    let W := weightWorkspaceWidth P q (2*q+8) t u
    let B := (haloLengthGroup s t band a b L).length
    conditionalHaloGroupPreparationWorkspace P N q l s t u band a b L ≤
      9*tblC V V+
      10000*(P+N+q+l+s+t+u+band+a+b+L+B+1)*(V+W+q+1) := by
  dsimp only
  unfold conditionalHaloGroupPreparationWorkspace installHaloGroupHeadersCost installGroupHeadersCost
    probeGeometryHaloGatherWorkspace prepareGeometryHaloClassWorkspace preparedHaloClassWorkspace
    haloClassHeadersCost haloClassControllerWorkspace countedOriginWorkspace
    generateHaloGeometryWidthCost completeGeometryHaloGatherWorkspace preparedOriginAdvanceWorkspace
    widenGeometryOriginsCost weightWidthCost
  dsimp only
  split <;> (ring_nf; omega)

theorem conditionalHaloGroupPreparationWorkspace_le_uniform
    (P N q l s t u band a b L : ℕ) (ha : a ≤ s) (hb : b ≤ s) (hL : L ≤ s) :
    let V := haloGeometryWidth t (2*q+8)
    let W := weightWorkspaceWidth P q (2*q+8) t u
    conditionalHaloGroupPreparationWorkspace P N q l s t u band a b L ≤
      9*tblC V V+50000*(P+N+q+l+s+t+u+band+1)*(V+W+q+1) := by
  apply (conditionalHaloGroupPreparationWorkspace_le_volume P N q l s t u band a b L).trans
  have hB := haloLengthGroup_length_le s t band a b L
  have hsum : P+N+q+l+s+t+u+band+a+b+L+(haloLengthGroup s t band a b L).length+1 ≤
      5*(P+N+q+l+s+t+u+band+1) := by omega
  calc
    _ ≤ 9*tblC (haloGeometryWidth t (2*q+8)) (haloGeometryWidth t (2*q+8))+
        10000*(5*(P+N+q+l+s+t+u+band+1))*
          (haloGeometryWidth t (2*q+8)+weightWorkspaceWidth P q (2*q+8) t u+q+1) := by gcongr
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
