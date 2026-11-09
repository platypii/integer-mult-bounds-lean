module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherConsecutive
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule

/-! Consecutive core publication has one repeated symbol stride, including
its initial skip. The control builder only needs the row count and packet. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

theorem originAdvances_consecutive (width W k N : ℕ) :
    originAdvances W (k*width) ((List.range' (k+1) N).map (·*width)) = List.replicate N (width*W) := by
  induction N generalizing k with
  | zero => rfl
  | succ N ih =>
    simp only [List.range'_succ,List.map_cons,originAdvances,List.replicate_succ,ih]
    simp [Nat.add_mul]

theorem fullGatherPublication_advances (s width radius W : ℕ) (hw : 0 < width)
    (hr : 0 < radius) (hrw : radius ≤ width) (hroom : 3*width ≤ s) :
    let g := gatherPublicationClass s width radius (width+2*radius)
    let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
    originAdvances W 0 windows.origins = List.replicate g.indices.length (g.length*W) := by
  dsimp only
  have hindices := fullCoreGather_consecutive s width radius hw hr hrw hroom
  have hlength : (gatherPublicationClass s width radius (width+2*radius)).length = width :=
    Nat.add_sub_cancel_right _ _
  simp only [coreSubsetPublicationWindows,PublicationWindows.restrict,gatherPublicationClass,coreStart,
    hindices,List.length_range',Nat.add_sub_cancel_right]
  change originAdvances W 0 ((List.range' 1 ((s-radius)/width-1)).map (fun k => k*width)) = _
  simpa only [Nat.zero_mul,Nat.zero_add] using originAdvances_consecutive width W 0 ((s-radius)/width-1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
