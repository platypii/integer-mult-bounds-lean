import IntegerMultBounds.Networks.GroupedCoefficients
import IntegerMultBounds.Networks.RationalScalarGrid
import IntegerMultBounds.Networks.GaussianFrameGrid
import IntegerMultBounds.Networks.GaussianBoundedMotif
import IntegerMultBounds.Networks.ComplexFramedExecution
import IntegerMultBounds.Machine.ActivePrefixStageParameters

/-! Exact scalar-prefix grids for the actual labeled complex25 grouped
network. Prefix states retain their true role frames; the frame's own grid
budget is derived from the finite Walsh definition, not a supplied contract. -/
namespace IntegerMultBounds.Machine.CompactFramedScalarGrid
noncomputable section
attribute [local irreducible] IntegerMultBounds.Networks.ComplexRank25.program
  IntegerMultBounds.Networks.GlobalGrouped.program IntegerMultBounds.Networks.GlobalGrouped.stage
  IntegerMultBounds.Networks.GlobalGrouped.partialStage IntegerMultBounds.Networks.GlobalGrouped.invocationGroups
  IntegerMultBounds.Networks.GlobalGrouped.localGroups
open Networks Networks.GaussianPrecision
open ComplexFramedExecution (Wire frameOf)

def coeffGood (c : ℚ) := BoundedGrid 1 52 (c:ℂ)

theorem group_coefficients : GroupedCoefficients.AllGroups coeffGood
    (ComplexRank25.program.map GroupedFrames.Vertex.group) := by
  rw [ComplexRank25.program_groups]
  unfold GlobalGrouped.complexProgram
  refine GroupedCoefficients.global coeffGood (fun c hc => by
    simpa only [coeffGood,Rat.cast_neg] using bounded_neg hc) ?_ ?_
    ComplexRank25.triples ComplexRank25.pairs (Equiv.refl (Fin 26)) _ _ _ _ ?_ ?_ ?_
  · simpa only [coeffGood,Rat.cast_zero] using bounded_zero 1 52
  · simpa only [coeffGood,Rat.cast_one,Int.cast_one,Nat.zero_add] using
      bound_mono (by norm_num : 1*2^1≤52) (bounded_raise (bounded_int 1 1 (by norm_num)) 1)
  · intro i j
    exact bound_mono (by norm_num : 1*2^1≤52)
      (bounded_raise (bounded_complexGather (fun i => (ComplexRank25.triples i).val) i j) 1)
  · intro i j
    exact bound_mono (by norm_num : 25+1≤52)
      (bounded_complexInject (GlobalCircuit.complexLocalPairs ComplexRank25.triples ComplexRank25.pairs) i j)
  · intro i j
    exact bound_mono (by norm_num : 1≤52)
      (bounded_complexScatter (fun i => (ComplexRank25.triples i).val) i j)

def rows (g : ℕ) := GroupedCircuit.compileGroups
  ((ComplexRank25.program.take g).map GroupedFrames.Vertex.group)
def bound (g M : ℕ) := scalarBound 1 52 (RationalScalarGrid.castRows (rows g)) M

theorem row_coefficients (g : ℕ) : CircuitCoefficients.All coeffGood (rows g) := by
  apply GroupedCoefficients.compileGroups
  intro v hv
  obtain ⟨v0,hv0,rfl⟩ := List.mem_map.mp hv
  exact group_coefficients _ (List.mem_map.mpr ⟨v0,List.mem_of_mem_take hv0,rfl⟩)

@[irreducible] def growthConstant := scalarBound 1 52
  (RationalScalarGrid.castRows ComplexFramedExecution.rows) 1

theorem rows_split (g : ℕ) : rows g++GroupedCircuit.compileGroups
    ((ComplexRank25.program.drop g).map GroupedFrames.Vertex.group)=ComplexFramedExecution.rows := by
  simp only [rows,ComplexFramedExecution.rows,GroupedCircuit.compileGroups,
    ←List.flatMap_append,←List.map_append,List.take_append_drop]

theorem bound_le (g M C : ℕ) (hC : growthConstant≤C) : bound g M≤M*C := by
  let tail := GroupedCircuit.compileGroups ((ComplexRank25.program.drop g).map GroupedFrames.Vertex.group)
  have hs : RationalScalarGrid.castRows (rows g)++RationalScalarGrid.castRows tail=
      RationalScalarGrid.castRows ComplexFramedExecution.rows := by
    simp only [RationalScalarGrid.castRows,←List.map_append]
    exact congrArg RationalScalarGrid.castRows (rows_split g)
  have h := scalarBound_ge 1 52 (RationalScalarGrid.castRows tail)
    (scalarBound 1 52 (RationalScalarGrid.castRows (rows g)) M)
  rw [←scalarBound_append,hs] at h
  calc
    _ ≤ scalarBound 1 52 (RationalScalarGrid.castRows ComplexFramedExecution.rows) M := h
    _ = M*growthConstant := by
      unfold growthConstant
      exact scalarBound_linear _ _ _ _
    _ ≤ M*C := Nat.mul_le_mul_left M hC

def initialLabels : Wire → ComplexPhaseBudget.Label := GlobalLabels.source ComplexRank25.vector
def labels (g : ℕ) := GroupedFrames.finalLabels initialLabels (ComplexRank25.program.take g)
def prefixProgram (k g : ℕ) := GroupedModuleFrames.compile (frameOf k) initialLabels (ComplexRank25.program.take g)
def profile (k g : ℕ) := GroupedModuleFrames.profile (frameOf k) (labels g)

theorem prefix_exact (k g : ℕ) (x : Wire → BinaryColumns.Arrays (25^3) k) :
    FramedCircuit.run (prefixProgram k g)
      (FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) initialLabels) x)=
      FramedCircuit.encode (profile k g) (FramedCircuit.moduleRun (rows g) x) :=
  GroupedModuleFrames.compile_invariant (frameOf k) initialLabels (ComplexRank25.program.take g) x

/-- The current actual role frames decode to an explicitly bounded scalar
prefix, including every scratch role and every original column address. -/
theorem decoded_grid (k g n M : ℕ) (x : Wire → BinaryColumns.Arrays (25^3) k)
    (hx : ∀ i ω,BoundedGrid n M (x i ω)) (i : Wire) (ω : BinaryColumns.Address (25^3) k) :
    BoundedGrid (n+(rows g).length) (bound g M)
      (FramedCircuit.decode (profile k g)
        (FramedCircuit.run (prefixProgram k g)
          (FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) initialLabels) x)) i ω) := by
  rw [prefix_exact,FramedCircuit.decode_encode]
  simpa only [Nat.mul_one,bound] using RationalScalarGrid.bounded (rows g) x n 1 M 52 hx (row_coefficients g) i ω

/-- Applying each role's actually retained frame adds at most the original
coordinate volume in precision and twice that volume in numerator growth. -/
theorem stored_grid (k g n M : ℕ) (x : Wire → BinaryColumns.Arrays (25^3) k)
    (hx : ∀ i ω,BoundedGrid n M (x i ω)) (i : Wire) (ω : BinaryColumns.Address (25^3) k) :
    BoundedGrid (n+(rows g).length+k*(25^3)) (bound g M*4^(k*(25^3)))
      (FramedCircuit.run (prefixProgram k g)
        (FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) initialLabels) x) i ω) := by
  rw [prefix_exact]
  exact bounded_rational_label_frame ComplexPhaseBudget.coordinateSymm _ _
    (fun ω => by
      simpa only [Nat.mul_one,bound] using RationalScalarGrid.bounded (rows g) x n 1 M 52 hx (row_coefficients g) i ω) ω

section TracePrefixes
attribute [local instance] Classical.propDecidable

private theorem compile_append {ι L R E : Type*} [DecidableEq ι] [CommRing R]
    [DecidableEq R] [AddCommGroup E] [Module R E]
    (frame : L → FramedCircuit.Frame R E) (current : ι → L)
    (vs ws : List (GroupedFrames.Vertex ι L R)) :
    GroupedModuleFrames.compile frame current (vs++ws) =
      GroupedModuleFrames.compile frame current vs ++
        GroupedModuleFrames.compile frame (GroupedFrames.finalLabels current vs) ws := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.cons_append,GroupedModuleFrames.compile,GroupedFrames.finalLabels,
      ih,List.append_assoc]

private theorem edges_append {ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (current desired : ι → FramedCircuit.Frame R E)
    (xs ys : List ι) :
    FramedCircuit.edges current desired (xs++ys) =
      FramedCircuit.edges current desired xs ++
        FramedCircuit.edges (FramedCircuit.afterEdges current desired xs) desired ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.cons_append,FramedCircuit.edges,FramedCircuit.afterEdges,ih]

def vertex (g : Fin ComplexRank25.program.length) := ComplexRank25.program[g.val]
def edgeWires (g : Fin ComplexRank25.program.length) (e : ℕ) :=
  (GroupedCircuit.touched (vertex g).group).take e

def edgeLabels (g : Fin ComplexRank25.program.length) (e : ℕ) (i : Wire) :=
  if i ∈ edgeWires g e then (vertex g).label else labels g.val i

def alignmentProgram (k : ℕ) (g : Fin ComplexRank25.program.length) (e : ℕ) :=
  prefixProgram k g.val ++ FramedCircuit.edges (profile k g.val)
    (fun _ => frameOf k (vertex g).label) (edgeWires g e)

theorem alignment_profile (k : ℕ) (g : Fin ComplexRank25.program.length) (e : ℕ) :
    FramedCircuit.afterEdges (profile k g.val) (fun _ => frameOf k (vertex g).label)
      (edgeWires g e) = GroupedModuleFrames.profile (frameOf k) (edgeLabels g e) := by
  funext i
  rw [FramedCircuit.afterEdges_apply]
  change _ = frameOf k (if i ∈ edgeWires g e then (vertex g).label else labels g.val i)
  split_ifs <;> rfl

/-- The state immediately before an actual listed edge call has the exact
retained role labels and the same logical scalar prefix. -/
theorem alignment_exact (k : ℕ) (g : Fin ComplexRank25.program.length) (e : ℕ)
    (x : Wire → BinaryColumns.Arrays (25^3) k) :
    FramedCircuit.run (alignmentProgram k g e)
      (FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) initialLabels) x) =
      FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) (edgeLabels g e))
        (FramedCircuit.moduleRun (rows g.val) x) := by
  rw [alignmentProgram,FramedCircuit.run_append,prefix_exact,
    FramedCircuit.edges_invariant,alignment_profile]

/-- Alignment changes actual stored frames, without introducing any new
logical scalar rows or any assumed recursive execution certificate. -/
theorem alignment_stored_grid (k n M : ℕ) (g : Fin ComplexRank25.program.length)
    (e : ℕ) (x : Wire → BinaryColumns.Arrays (25^3) k)
    (hx : ∀ i ω,BoundedGrid n M (x i ω)) (i : Wire)
    (ω : BinaryColumns.Address (25^3) k) :
    BoundedGrid (n+(rows g.val).length+k*(25^3)) (bound g.val M*4^(k*(25^3)))
      (FramedCircuit.run (alignmentProgram k g e)
        (FramedCircuit.encode (GroupedModuleFrames.profile (frameOf k) initialLabels) x) i ω) := by
  rw [alignment_exact]
  exact bounded_rational_label_frame ComplexPhaseBudget.coordinateSymm _ _
    (fun ω => by
      simpa only [Nat.mul_one,bound] using RationalScalarGrid.bounded (rows g.val)
        x n 1 M 52 hx (row_coefficients g.val) i ω) ω

private theorem compile_alignment_prefix {ι L R E : Type*} [DecidableEq ι]
    [CommRing R] [DecidableEq R] [AddCommGroup E] [Module R E]
    (frame : L → FramedCircuit.Frame R E) (current : ι → L)
    (vs : List (GroupedFrames.Vertex ι L R)) (g : Fin vs.length) (e : ℕ) :
    ∃ rest, GroupedModuleFrames.compile frame current vs =
      (GroupedModuleFrames.compile frame current (vs.take g.val) ++
        FramedCircuit.edges
          (GroupedModuleFrames.profile frame (GroupedFrames.finalLabels current (vs.take g.val)))
          (fun _ => frame vs[g.val].label) ((GroupedCircuit.touched vs[g.val].group).take e)) ++ rest := by
  let v := vs[g.val]
  let labels := GroupedFrames.finalLabels current (vs.take g.val)
  let prof := GroupedModuleFrames.profile frame labels
  let desired : ι → FramedCircuit.Frame R E := fun _ => frame v.label
  let touched := GroupedCircuit.touched v.group
  let after := FramedCircuit.afterEdges prof desired (touched.take e)
  let tail := GroupedModuleFrames.compile frame (GroupedFrames.after labels v) (vs.drop (g.val+1))
  refine ⟨FramedCircuit.edges after desired (touched.drop e) ++
    (GroupedCircuit.compile v.group).map FramedCircuit.Instruction.gate ++ tail, ?_⟩
  have split : vs = vs.take g.val ++ v :: vs.drop (g.val+1) := by
    conv_lhs => rw [←List.take_append_drop g.val vs]
    rw [List.drop_eq_getElem_cons g.isLt]
  have hc := congrArg (GroupedModuleFrames.compile frame current) split
  rw [compile_append,GroupedModuleFrames.compile,GroupedCircuit.compileFramed] at hc
  rw [hc]
  have he := edges_append prof desired (touched.take e) (touched.drop e)
  rw [List.take_append_drop] at he
  change GroupedModuleFrames.compile frame current (vs.take g.val) ++
    (FramedCircuit.edges prof desired touched ++
      (GroupedCircuit.compile v.group).map FramedCircuit.Instruction.gate ++ tail) = _
  rw [he]
  simp only [prof,labels,desired,touched,v,after,List.append_assoc]

/-- Each alignment boundary is a literal prefix of the original complete
compiler, including its actual ordered edge instructions and terminal edges. -/
theorem alignment_prefix (k : ℕ) (g : Fin ComplexRank25.program.length) (e : ℕ) :
    ∃ rest, ComplexFramedExecution.network k = alignmentProgram k g e ++ rest := by
  obtain ⟨rest,hr⟩ := compile_alignment_prefix (frameOf k) initialLabels ComplexRank25.program g e
  let sink := FramedCircuit.edges
    (GroupedModuleFrames.profile (frameOf k)
      (GroupedFrames.finalLabels initialLabels ComplexRank25.program))
    (GroupedModuleFrames.profile (frameOf k)
      (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector)) ComplexRank25.wires
  refine ⟨rest++sink, ?_⟩
  change GroupedModuleFrames.compile (frameOf k) initialLabels ComplexRank25.program ++ sink = _
  rw [hr]
  change (alignmentProgram k g e ++ rest) ++ sink = alignmentProgram k g e ++ (rest++sink)
  exact List.append_assoc _ _ _

end TracePrefixes

/-- Original node geometry derives the frame depth directly. -/
theorem frame_depth_le {s : CompactGadgetReservationShape.Shape}
    (v : ActivePrefixStageParameters.Stage s) (hslots : v.slots=25^3) : v.f*(25^3)≤s.active := by
  have h := v.activeAxes
  rw [hslots] at h
  nlinarith

end
end IntegerMultBounds.Machine.CompactFramedScalarGrid
