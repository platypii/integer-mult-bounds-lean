import IntegerMultBounds.Networks.Shared50GlobalShear

/-! Rational source/target operators behind every physical signed frame edge.
Keeping both endpoints makes reduction modulo a common good prime compositional;
the difference list remains exactly the already-counted actual operator list. -/

namespace IntegerMultBounds.Networks.Shared50OperatorPairs

noncomputable section
open Shared50GlobalTrace
open Shared50GlobalBudget (World Ambient Triple)
open Shared50ShearEndpoints (projector)

variable {n : ℕ}
abbrev End := Ambient →ₗ[ℚ] Ambient

def boundary : List (End × End) :=
  wires.map (fun i => (-projector (source i),projector (input 0 i)))

def tail (e : Fin n ≃ Triple) : List (End × End) :=
  (RankTrace.edges (input 0) (Shared50GlobalShear.tailUpdates e)).map
    (fun p => (projector p.1,projector p.2))

def pairs (e : Fin n ≃ Triple) : List (End × End) := boundary ++ tail e

theorem differences (e : Fin n ≃ Triple) :
    (pairs e).map (fun p => p.2 - p.1) = Shared50GlobalShear.operators e := by
  simp only [pairs,boundary,tail,List.map_append,List.map_map,Shared50GlobalShear.operators,
    Shared50SignedBoundary.operators,Shared50GlobalShear.tailOperators,
    Shared50InvocationProjectionRank.operators]
  rfl

/-- Actual physical edge pairs are exactly the shears of these operator endpoints. -/
theorem physical_pairs (e : Fin n ≃ Triple) :
    FramedEdgeTrace.pairs (Shared50GlobalShear.program e) =
      (pairs e).map (fun p => (ShearFrame.frame p.1,ShearFrame.frame p.2)) := by
  simp only [Shared50GlobalShear.program,FramedEdgeTrace.pairs_append,
    Shared50SignedBoundary.physical_pairs,Shared50GlobalShear.tail_pairs,
    pairs,boundary,tail,List.map_append,List.map_map]
  rfl

end
end IntegerMultBounds.Networks.Shared50OperatorPairs
