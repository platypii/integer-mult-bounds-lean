import IntegerMultBounds.Machine.CompactComplexScalarSequenceSemantics
import IntegerMultBounds.Machine.CompactComplexScalarLifecycleGrid

/-! Literal named scalar blocks at actual grouped-network boundaries. Their
prefix and suffix are generated from the original vertex list, rather than
supplied through a segment equality or recomputed by concrete enumeration. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarSegmentRows
noncomputable section
open Networks
open CompactComplexScalarIntegerRows (GroupIndex RowIndex Wire gates gate)
open CompactComplexScalarSequenceSemantics (circuit)
attribute [local irreducible] ComplexRank25.program CompactComplexScalarIntegerRows.gates
  ComplexFramedExecution.rows

/-- The genuine ordered row names executed after one vertex's alignment. -/
def block (g : GroupIndex) : List RowIndex :=
  List.ofFn (fun r : Fin (gates g).length => ⟨g,r⟩)

/-- All groups preceding this alignment boundary. -/
def before (g : GroupIndex) := RationalScalarGrid.castRows (CompactFramedScalarGrid.rows g.val)

/-- All groups following this scalar completion boundary. -/
def after (g : GroupIndex) := RationalScalarGrid.castRows
  (GroupedCircuit.compileGroups
    ((ComplexRank25.program.drop (g.val+1)).map GroupedFrames.Vertex.group))

private theorem block_map {α : Type*} (g : GroupIndex) (f : Circuit.Gate Wire ℚ → α) :
    (block g).map (fun r => f (gate r))=(gates g).map f := by
  rw [block,List.map_ofFn]
  exact List.ofFn_getElem_eq_map (gates g) f

/-- Names, order and sparse rows match the actual grouped scalar compiler. -/
theorem block_circuit (g : GroupIndex) :
    circuit (block g)=RationalScalarGrid.castRows (gates g) :=
  block_map g RationalScalarGrid.castGate

private theorem split_at {α β : Type*} (xs : List α) (f : α → List β)
    (g : Fin xs.length) :
    (xs.take g.val).flatMap f++f xs[g.val]++(xs.drop (g.val+1)).flatMap f=xs.flatMap f := by
  have hs : xs=xs.take g.val++xs[g.val]::xs.drop (g.val+1) := by
    conv_lhs => rw [←List.take_append_drop g.val xs]
    rw [List.drop_eq_getElem_cons g.isLt]
  conv_rhs => rw [hs]
  simp only [List.flatMap_append,List.flatMap_cons,List.append_assoc]

/-- The actual scalar block's full-network interval is derived from its
original group index, without a caller-supplied decomposition. -/
theorem segment (g : GroupIndex) :
    before g++circuit (block g)++after g=
      RationalScalarGrid.castRows ComplexFramedExecution.rows := by
  have hs := split_at ComplexRank25.program
    (fun v => GroupedCircuit.compile v.group) g
  rw [block_circuit]
  unfold before after RationalScalarGrid.castRows
  rw [←List.map_append,←List.map_append]
  apply congrArg (List.map RationalScalarGrid.castGate)
  simpa only [CompactFramedScalarGrid.rows,CompactComplexScalarIntegerRows.gates,
    CompactFramedScalarGrid.vertex,ComplexFramedExecution.rows,GroupedCircuit.compileGroups,
    List.flatMap_map,Function.comp_def] using hs

private theorem prefix_step {α β : Type*} (xs : List α) (f : α → List β)
    (g : Fin xs.length) :
    (xs.take (g.val+1)).flatMap f=(xs.take g.val).flatMap f++f xs[g.val] := by
  rw [List.take_succ_eq_append_getElem g.isLt,List.flatMap_append]
  simp only [List.flatMap_singleton]

/-- Completing the physical block reaches precisely the next original scalar
prefix used by the dynamic frame and denominator ledger. -/
theorem prefix_complete (g : GroupIndex) :
    before g++circuit (block g)=
      RationalScalarGrid.castRows (CompactFramedScalarGrid.rows (g.val+1)) := by
  have hs := prefix_step ComplexRank25.program
    (fun v => GroupedCircuit.compile v.group) g
  rw [block_circuit]
  unfold before RationalScalarGrid.castRows
  rw [←List.map_append]
  apply congrArg (List.map RationalScalarGrid.castGate)
  simpa only [CompactFramedScalarGrid.rows,CompactComplexScalarIntegerRows.gates,
    CompactFramedScalarGrid.vertex,GroupedCircuit.compileGroups,List.flatMap_map,
    Function.comp_def] using hs.symm


/-- The physical row count is exactly the original compiled group length. -/
theorem block_length (g : GroupIndex) : (block g).length=(gates g).length := by
  simp only [block,List.length_ofFn]

/-- The genuine scalar completion advances the retained prefix ledger by
exactly the number of physical denominator increments in this block. -/
theorem prefix_length (g : GroupIndex) :
    (CompactFramedScalarGrid.rows (g.val+1)).length=
      (CompactFramedScalarGrid.rows g.val).length+(block g).length := by
  have h := congrArg List.length (prefix_complete g)
  simpa only [before,circuit,RationalScalarGrid.castRows,List.length_append,List.length_map] using h.symm

variable {s : ℕ}
open CompactComplexScalarCountLifecycle (Realizes program output)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarSequenceSemantics (values)
open CompactComplexScalarPathGuard (budget)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open CompactComplexScalarIntegerRows (guardBits)
open Networks.GaussianPrecision (BoundedGrid)
open ButterflyStreamData (Coefficient)

/-- The actual named grouped scalar block executes with generated count and
clean private tapes. Its prefix comes from the original group boundary and
its live denominator advances by exactly that group's listed scalar rows. -/
theorem group_runs_from_path {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hcapacity : n≤ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hgrid : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh (block g)) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute (block g) data) (n+(gates g).length))
      (CompactComplexScalarCountLifecycle.timeConstant (block g)*
        (ActivePrefixStageTripleWords.count inp*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    ∀ i wire,BoundedGrid (n+(gates g).length)
      (budget p C levels frames returned axes)
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        (CompactComplexScalarPolynomialSequence.execute (block g) data) i wire) := by
  have hroom' : dependencyCoefficient C+Nat.clog 2 (C+1)+
      (block g).length*guardBits≤sh.chunk := by
    simpa only [block_length] using hroom
  have h := CompactComplexScalarLifecycleGrid.runs_prefix_linear_from_path path inp
    hs header hh (block g) ell p C axes metadataP n control queue scalar tail storage payload
    xs hw hblank hsource hlive ha hp haxes hroom' hcapacity (before g) (after g)
    (segment g) hC hgrid
  simpa only [block_length] using h

end
end IntegerMultBounds.Machine.CompactComplexScalarSegmentRows
