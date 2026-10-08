import IntegerMultBounds.Networks.GroupedCircuit
import IntegerMultBounds.Networks.RankTrace

/-! A full common-frame compiler preserving the actual grouped boundaries.
Its per-wire label history is precisely the history used by rank accounting. -/

namespace IntegerMultBounds.Networks.GroupedFrames

open GroupedCircuit
variable {ι L R Ω : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]

structure Vertex (ι L R : Type*) [CommRing R] where
  group : Group ι R
  label : L

def touches (v : Vertex ι L R) : List (ι × L) :=
  (touched v.group).map fun i => (i, v.label)

def after (current : ι → L) (v : Vertex ι L R) : ι → L :=
  RankTrace.finish current (touches v)

def finalLabels (current : ι → L) : List (Vertex ι L R) → ι → L
  | [] => current
  | v :: rest => finalLabels (after current v) rest

def updates (vs : List (Vertex ι L R)) : List (ι × L) := vs.flatMap touches

theorem finalLabels_trace (current : ι → L) (vs : List (Vertex ι L R)) :
    finalLabels current vs = RankTrace.finish current (updates vs) := by
  induction vs generalizing current with
  | nil => rfl
  | cons v rest ih =>
    simp only [finalLabels, updates, List.flatMap_cons, RankTrace.finish_append, ih, after, touches]

variable (frameOf : L → FramedCircuit.Frame R (Ω → R))

def profile (current : ι → L) : ι → FramedCircuit.Frame R (Ω → R) := fun i => frameOf (current i)

theorem after_profile (current : ι → L) (v : Vertex ι L R) :
    FramedCircuit.afterEdges (profile frameOf current) (fun _ => frameOf v.label) (touched v.group) =
      profile frameOf (after current v) := by
  funext i
  rw [FramedCircuit.afterEdges_apply]
  change (if i ∈ touched v.group then frameOf v.label else frameOf (current i)) =
    frameOf (RankTrace.finish current ((touched v.group).map fun j => (j, v.label)) i)
  rw [RankTrace.finish_align]
  split_ifs <;> rfl

def compile (current : ι → L) : List (Vertex ι L R) → List (FramedCircuit.Instruction ι R (Ω → R))
  | [] => []
  | v :: rest => compileFramed v.group (profile frameOf current) (frameOf v.label) ++
      compile (after current v) rest

/-- Every physical grouped gate runs at its one common label frame, and the
compiler tracks the label left at every actual touched wire. -/
theorem compile_invariant (current : ι → L) (vs : List (Vertex ι L R)) (x : ι → Ω → R) :
    FramedCircuit.run (compile frameOf current vs) (FramedCircuit.encode (profile frameOf current) x) =
      FramedCircuit.encode (profile frameOf (finalLabels current vs))
        (fun i ω => runGroups (vs.map Vertex.group) (fun j => x j ω) i) := by
  induction vs generalizing current x with
  | nil => rfl
  | cons v rest ih =>
    rw [compile, FramedCircuit.run_append, compileFramed_pointwise, after_profile, ih]
    rfl

def network (wires : List ι) (input output : ι → L) (vs : List (Vertex ι L R)) :
    List (FramedCircuit.Instruction ι R (Ω → R)) :=
  compile frameOf input vs ++ FramedCircuit.edges (profile frameOf (finalLabels input vs))
    (profile frameOf output) wires

/-- Full grouped common-frame identity on every wire and address, including
scratch/spectators; the input inverse is interpretation, not preprocessing. -/
theorem network_identity (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) (stored : ι → Ω → R) :
    FramedCircuit.run (network frameOf wires input output vs) stored =
      FramedCircuit.encode (profile frameOf output)
        (fun i ω => runGroups (vs.map Vertex.group)
          (fun j => (frameOf (input j)).symm (stored j) ω) i) := by
  have hfinal : FramedCircuit.afterEdges (profile frameOf (finalLabels input vs))
      (profile frameOf output) wires = profile frameOf output := by
    funext i
    simp [FramedCircuit.afterEdges_apply, hall i]
  conv_lhs => rw [← FramedCircuit.encode_decode (profile frameOf input) stored]
  rw [network, FramedCircuit.run_append, compile_invariant, FramedCircuit.edges_invariant, hfinal]
  rfl

/-- This is the exact label-update history of the compiler, including sinks. -/
def networkUpdates (wires : List ι) (output : ι → L) (vs : List (Vertex ι L R)) : List (ι × L) :=
  updates vs ++ wires.map fun i => (i, output i)

theorem network_trace_final (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) :
    RankTrace.finish input (networkUpdates wires output vs) = output := by
  funext i
  simp [networkUpdates, RankTrace.finish_append, RankTrace.finish_align, hall i]

/-- Projection ranks for this compiler's exact label history satisfy the
endpoint/loss identity. The premise checks every actual consecutive label;
the concrete loss enumeration is deliberately left to the network instance. -/
theorem projection_rank_balance {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] [Fintype ι] (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → RankTrace.Label B) (vs : List (Vertex ι (RankTrace.Label B) R))
    (hc : ∀ p ∈ RankTrace.edges input (networkUpdates wires output vs),
      p.1.space ≤ p.2.space ∨ p.2.space ≤ p.1.space) :
    ((RankTrace.edges input (networkUpdates wires output vs)).map
      fun p => RankTrace.edgeRank B hs p.1 p.2).sum + RankTrace.total (RankTrace.dimension B) input =
      RankTrace.total (RankTrace.dimension B) output +
        2 * RankTrace.loss (RankTrace.dimension B) input (networkUpdates wires output vs) := by
  simpa only [network_trace_final wires hall input output vs] using
    RankTrace.rank_balance B hs input (networkUpdates wires output vs) hc

end IntegerMultBounds.Networks.GroupedFrames
