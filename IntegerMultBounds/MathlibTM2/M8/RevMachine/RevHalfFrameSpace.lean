module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfCallBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegmentBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyLeafWithin

/-! Fixed local reserve coefficients for the reversed-family frame. The
segment allowance is the maximum over the fixed schedule, never a runtime sum. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (volume)
noncomputable section

def prepareSpaceConstant (N : RevNetwork) : ℕ :=
  4000+BinaryDescriptorDivMod.linearConstant (bits N.width)

def scheduleSpaceConstant (N : RevNetwork) : ℕ := Finset.univ.sup
  (fun i : Fin (pcs N).length => match (pcs N)[i] with
    | .seg s => RevNode.segSpaceConstant N s
    | .call _ => 0)

theorem segment_space_le (N : RevNetwork) (i : Graph.Site (pcs N))
    (s : Schedule.Seg (N.World ⊕ N.Temp) N.width) (hi : (pcs N)[i] = .seg s) :
    RevNode.segSpaceConstant N s ≤ scheduleSpaceConstant N := by
  have h := Finset.le_sup (f := fun i : Fin (pcs N).length => match (pcs N)[i] with
    | .seg s => RevNode.segSpaceConstant N s
    | .call _ => 0) (Finset.mem_univ i)
  simpa only [hi,scheduleSpaceConstant] using h

structure FrameReserve (N : RevNetwork) (k C D : ℕ) : Prop where
  prepare : prepareSpaceConstant N ≤ D
  leaf : Family.leafSpaceConstant C+1 ≤ D
  split : NodeSplit.splitSpaceConstant N+1 ≤ D
  segment : 36+scheduleSpaceConstant N ≤ D
  merge : 36+NodeSplit.mergeSpaceConstant N ≤ D
  call : 2*(36+callSpaceConstant N k) ≤ D
  finish : 23 ≤ D
  pop : k+2 ≤ D

def frameSpaceConstant (N : RevNetwork) (k C : ℕ) : ℕ :=
  max (prepareSpaceConstant N) (max (Family.leafSpaceConstant C+1)
    (max (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N)
      (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max 23 (k+2)))))))

theorem frame_reserve (N : RevNetwork) (k C : ℕ) :
    FrameReserve N k C (frameSpaceConstant N k C) := by
  have hLeaf := le_max_right (prepareSpaceConstant N) (max (Family.leafSpaceConstant C+1) (max (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))))))
  have hSplit := (le_max_right (Family.leafSpaceConstant C+1) (max (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2))))))).trans hLeaf
  have hSegment := (le_max_right (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))))).trans hSplit
  have hMerge := (le_max_right (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2))))).trans hSegment
  have hCall := (le_max_right (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))).trans hMerge
  have hFinish := (le_max_right (2*(36+callSpaceConstant N k)) (max (23) (k+2))).trans hCall
  have hPop := (le_max_right (23) (k+2)).trans hFinish
  constructor
  · exact le_max_left (prepareSpaceConstant N) (max (Family.leafSpaceConstant C+1) (max (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))))))
  · exact (le_max_left (Family.leafSpaceConstant C+1) (max (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2))))))).trans hLeaf
  · exact (le_max_left (NodeSplit.splitSpaceConstant N+1) (max (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))))).trans hSplit
  · exact (le_max_left (36+scheduleSpaceConstant N) (max (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2))))).trans hSegment
  · exact (le_max_left (36+NodeSplit.mergeSpaceConstant N) (max (2*(36+callSpaceConstant N k)) (max (23) (k+2)))).trans hMerge
  · exact (le_max_left (2*(36+callSpaceConstant N k)) (max (23) (k+2))).trans hCall
  · exact (le_max_left (23) (k+2)).trans hFinish
  · exact hPop

theorem preparation_cost_bound (N : RevNetwork)
    (v : RecursiveInterchangeLayout.Descriptor) (hp : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hn : 1 ≤ n) (hw : v.width = n*b) :
    Family.prepCost b N.width n ≤ prepareSpaceConstant N*volume prime v :=
  Family.prepCost_linear v hp b N.width n hb hn hw

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
