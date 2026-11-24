module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open IntervalDescriptor
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

theorem phaseChildRank_le (n : Fin 9) (run : StageRun) (j : MoveIndex) :
    nodeChildren5[(phaseChildPositions.choose (n,run,j)).val] ≤ 7 := by
  rw [(phaseChildPositions.choose_spec n run j).1]
  let edges := Geometry.Moves.phaseEdges.filter positiveMove
  let e := edges[j.val]
  have edge := List.mem_filter.mp (List.getElem_mem (l := edges) (n := j.val) j.isLt)
  have mem : Geometry.moveRank e.1 e.2 ∈ Geometry.Moves.phaseEdges.map (fun p => Geometry.moveRank p.1 p.2) :=
    List.mem_map.mpr ⟨e,edge.1,rfl⟩
  rw [Geometry.Moves.phase_ranks] at mem
  have paid := BitOccurrences.phase_perm.mem_iff.mp (List.mem_filter.mpr ⟨mem,by simpa [positiveMove,e] using edge.2⟩)
  exact (show ∀ r ∈ Layer.SelectedMoments.expand BitOccurrences.phaseHist, r ≤ 7 by decide +kernel) _ paid

/-- Every sweep invocation stops once seven atoms fit under the cutoff. -/
theorem sweepChildWidth_le (p : CutoffNodeInput) (n : Fin 9) (run : StageRun) {l r : ℕ}
    (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex) (j : Fin 3)
    (k : Fin (invocationCounts l r j)) :
    (scheduledChild prime p.node (invocationChildren n run pre post j k)).width ≤ 7*(p.w+1) := by
  change nodeChildren5[_]*(p.node.width/64) ≤ _
  rw [p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
  apply Nat.mul_le_mul_right
  fin_cases j
  · exact phaseChildRank_le n run (pre k)
  · exact (copyChildPosition_rank n run.1 run.2 k).le
  · exact phaseChildRank_le n run (post k)

end IntegerMultBounds.MathlibTM2.M6.BitNode
