import IntegerMultBounds.Networks.SharedPointFamily
import IntegerMultBounds.Networks.DAGReplayBudget
import IntegerMultBounds.Networks.DAGInstructionCount

/-! The actual globally shared fifty-copy circuit: replay each certified local
DAG into one persistent interned DAG and retain every remapped output reference.
The proof does not assume any global circuit list or allocation count. -/

namespace IntegerMultBounds.Networks.SharedPointReplay

open DisjointCircuit DisjointBuilder NeighborCounts DAGReplay

attribute [local irreducible] Paired49Certificate.nodes Certificates.Paired49.outputs
  Certificates.Paired49.entries Certificates.Paired49.bank DAGReplay.replay

/-- The actual input renaming for one common-point copy. -/
def embedding (c : Fin 50) : Fin 1176 ↪ Triple 50 :=
  ⟨SharedPointLift.source (SharedPointLift.pairPayload 49) (SharedPointLift.pairPayload_card 49) c,
    SharedPointLift.source_injective _ _ (SharedPointLift.pairPayload_injective 49) c⟩

@[simp] theorem map_embedding (c : Fin 50) (s : Finset (Fin 1176)) :
    s.map (embedding c) = SharedPointLift.lift49 c s := by
  rw [Finset.map_eq_image]
  rfl

structure Output where
  common : Fin 50
  pair : ℕ × ℕ
  ref : ℕ

structure State where
  nodes : List (Node (Triple 50))
  outputs : List Output

def expected (out : Output) : Finset (Triple 50) :=
  SharedPointLift.lift49 out.common (MaskDAG.decode (PairMask.exclusion49 out.pair.1 out.pair.2))

def CorrectOutput (nodes : List (Node (Triple 50))) (out : Output) : Prop :=
  (nodes.map Node.support)[out.ref]? = some (expected out)

def Ready (state : State) : Prop :=
  Valid state.nodes ∧ (state.nodes.map Node.support).Nodup ∧
    ∀ out ∈ state.outputs, CorrectOutput state.nodes out

/-- Import a source DAG with its designated output keys. -/
def importStep (source : List (Node (Fin 1176))) (localOutputs : List ((ℕ × ℕ) × ℕ))
    (state : State) (c : Fin 50) : State :=
  ⟨(replay (embedding c) state.nodes source).1,
    state.outputs ++ localOutputs.map (fun out =>
      ⟨c, out.1, (replay (embedding c) state.nodes source).2[out.2]?.getD 0⟩)⟩

private theorem importStep_nodes (source : List (Node (Fin 1176)))
    (localOutputs : List ((ℕ × ℕ) × ℕ)) (state : State) (c : Fin 50) :
    (importStep source localOutputs state c).nodes = (replay (embedding c) state.nodes source).1 := rfl

private theorem importStep_outputs (source : List (Node (Fin 1176)))
    (localOutputs : List ((ℕ × ℕ) × ℕ)) (state : State) (c : Fin 50) :
    (importStep source localOutputs state c).outputs = state.outputs ++ localOutputs.map (fun out =>
      (⟨c, out.1, (replay (embedding c) state.nodes source).2[out.2]?.getD 0⟩ : Output)) := rfl

/-- Import one local circuit and append its remapped designated outputs. -/
def step (state : State) (c : Fin 50) : State :=
  importStep Paired49Certificate.nodes Certificates.Paired49.outputs state c

@[simp] theorem step_nodes (state : State) (c : Fin 50) :
    (step state c).nodes = (replay (embedding c) state.nodes Paired49Certificate.nodes).1 :=
  importStep_nodes _ _ _ _

@[simp] theorem step_outputs (state : State) (c : Fin 50) :
    (step state c).outputs = state.outputs ++ Certificates.Paired49.outputs.map (fun out =>
      (⟨c, out.1, (replay (embedding c) state.nodes Paired49Certificate.nodes).2[out.2]?.getD 0⟩ : Output)) :=
  importStep_outputs _ _ _ _

/-- Process common points in their literal enumeration order. -/
def runFrom (state : State) : List (Fin 50) → State
  | [] => state
  | c :: common => runFrom (step state c) common

def initial : State := ⟨[], []⟩

def circuit : State := runFrom initial (List.finRange 50)

private theorem local_output_support (out : (ℕ × ℕ) × ℕ) (ho : out ∈ Certificates.Paired49.outputs) :
    ∃ hi : out.2 < Paired49Certificate.nodes.length,
      Paired49Certificate.nodes[out.2].support = MaskDAG.decode (PairMask.exclusion49 out.1.1 out.1.2) := by
  obtain ⟨hi, hm⟩ := Certificates.Paired49.output_spec out ho
  have hi' : out.2 < Paired49Certificate.nodes.length := by rw [Paired49Certificate.node_count]; exact hi
  refine ⟨hi', ?_⟩
  have hs := SharedPointFamily.localSupport_bank out.2 hi
  rw [SharedPointFamily.localSupport_get out.2 hi', hm, Option.getD_some] at hs
  exact hs

theorem step_ready (state : State) (c : Fin 50) (hs : Ready state) : Ready (step state c) := by
  obtain ⟨hv, hn, ho⟩ := hs
  rw [Ready, step_nodes, step_outputs]
  have hr := replay_correct (embedding c) state.nodes Paired49Certificate.nodes hv Paired49Certificate.valid
  refine ⟨hr.1, replay_nodup (embedding c) _ _ hn, ?_⟩
  intro out hout
  rcases List.mem_append.mp hout with hold | hnew
  · exact lookup_extends hr.2.1 (ho out hold)
  · obtain ⟨localOut, hlocal, rfl⟩ := List.mem_map.mp hnew
    obtain ⟨hi, hsupport⟩ := local_output_support localOut hlocal
    have hh := replay_support (embedding c) state.nodes Paired49Certificate.nodes hv
      Paired49Certificate.valid localOut.2 hi
    simpa only [CorrectOutput, expected, hsupport, map_embedding] using hh

theorem runFrom_ready (state : State) (common : List (Fin 50)) (hs : Ready state) :
    Ready (runFrom state common) := by
  induction common generalizing state with
  | nil => exact hs
  | cons c common ih => exact ih (step state c) (step_ready state c hs)

theorem ready : Ready circuit := runFrom_ready initial _ ⟨trivial, by simp [initial], by simp [initial]⟩

theorem valid : Valid circuit.nodes := ready.1

theorem supports_nodup : (circuit.nodes.map Node.support).Nodup := ready.2.1

theorem output_support (out : Output) (ho : out ∈ circuit.outputs) : CorrectOutput circuit.nodes out :=
  ready.2.2 out ho

theorem output_bound (out : Output) (ho : out ∈ circuit.outputs) : out.ref < circuit.nodes.length :=
  lookup_bound (output_support out ho)

/-- Actual imported execution computes every requested lifted support sum. -/
theorem output_value {A : Type*} [AddCommMonoid A] (input : Triple 50 → A)
    (out : Output) (ho : out ∈ circuit.outputs) :
    (eval input circuit.nodes)[out.ref]? = some (supportSum input (expected out)) := by
  rw [eval_eq input _ valid]
  have hh := congrArg (Option.map (supportSum input)) (output_support out ho)
  simpa only [CorrectOutput, ← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some] using hh

def key (out : Output) : Fin 50 × (ℕ × ℕ) := (out.common, out.pair)

theorem step_keys (state : State) (c : Fin 50) :
    (step state c).outputs.map key = state.outputs.map key ++
      (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair)) := by
  simp only [step_outputs, List.map_append, List.map_map]
  rw [← Certificates.Paired49.output_keys]
  simp only [List.map_map, Function.comp_def, key]

theorem runFrom_keys (state : State) (common : List (Fin 50)) :
    (runFrom state common).outputs.map key = state.outputs.map key ++
      common.flatMap (fun c => (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair))) := by
  induction common generalizing state with
  | nil => simp [runFrom]
  | cons c common ih => simp only [runFrom, ih, step_keys, List.flatMap_cons, List.append_assoc]

/-- Every canonical pair output appears once per actual common-point copy. -/
theorem output_keys : circuit.outputs.map key =
    (List.finRange 50).flatMap (fun c =>
      (PairedCircuit.pairs (List.range 49)).map (fun pair => (c,pair))) := by
  simpa only [circuit, initial, List.map_nil, List.nil_append] using runFrom_keys initial (List.finRange 50)

theorem step_output_count (state : State) (c : Fin 50) :
    (step state c).outputs.length = state.outputs.length + 1176 := by
  simp only [step_outputs, List.length_append, List.length_map, Certificates.Paired49.output_count]

theorem runFrom_output_count (state : State) (common : List (Fin 50)) :
    (runFrom state common).outputs.length = state.outputs.length + common.length * 1176 := by
  induction common generalizing state with
  | nil => simp [runFrom]
  | cons c common ih =>
    rw [runFrom, ih, step_output_count, List.length_cons]
    omega

theorem output_count : circuit.outputs.length = 58800 := by
  rw [circuit, runFrom_output_count]
  simp [initial]

/-- The certified support family bounds every newly imported addition. -/
theorem local_addition_mem (c : Fin 50) (s : Finset (Fin 1176))
    (hs : AdditionSupport Paired49Certificate.nodes s) :
    s.map (embedding c) ∈ SharedPointFamily.domain.image SharedPointFamily.support := by
  obtain ⟨node, hn, hk, he⟩ := hs
  obtain ⟨i, hi, hnode⟩ := List.mem_iff_getElem.mp hn
  have hd : (c,i) ∈ SharedPointFamily.domain := by
    apply (SharedPointFamily.mem_domain_iff (c,i)).mpr
    exact ⟨node, (List.getElem?_eq_getElem hi).trans (congrArg some hnode), hk⟩
  refine Finset.mem_image.mpr ⟨(c,i), hd, ?_⟩
  rw [SharedPointFamily.support, SharedPointFamily.localSupport_get i hi, hnode, he, map_embedding]

/-- All actual additions, including those from earlier copies, stay in the
finite source-support budget. -/
def Contained (state : State) : Prop :=
  ∀ s, AdditionSupport state.nodes s → s ∈ SharedPointFamily.domain.image SharedPointFamily.support

theorem step_contained (state : State) (c : Fin 50) (hs : Contained state) : Contained (step state c) := by
  rw [Contained, step_nodes]
  intro s hnew
  rcases replay_additionSupport (embedding c) state.nodes Paired49Certificate.nodes s hnew with
    hold | ⟨localSupport, hlocal, he⟩
  · exact hs s hold
  · exact he ▸ local_addition_mem c localSupport hlocal

theorem runFrom_contained (state : State) (common : List (Fin 50)) (hs : Contained state) :
    Contained (runFrom state common) := by
  induction common generalizing state with
  | nil => exact hs
  | cons c common ih => exact ih _ (step_contained state c hs)

theorem contained : Contained circuit := runFrom_contained initial _ (by
  rintro s ⟨node, hn, _⟩
  simp [initial] at hn)

/-- Actual requested output references in their common-point/pair order. -/
def outputRefs : List ℕ := circuit.outputs.map Output.ref

attribute [local irreducible] circuit

theorem outputRefs_count : outputRefs.length = 58800 := by
  rw [outputRefs, List.length_map, output_count]

theorem outputRefs_bounds : ∀ i ∈ outputRefs, i < circuit.nodes.length := by
  intro i hi
  obtain ⟨out, ho, rfl⟩ := List.mem_map.mp hi
  exact output_bound out ho

theorem additionSupports_subset : DAGReplayBudget.additionSupports circuit.nodes ⊆
    SharedPointFamily.domain.image SharedPointFamily.support := by
  intro s hs
  exact contained s ((DAGReplayBudget.mem_additionSupports _ _).mp hs)

/-- Support sharing bounds the actual addition nodes of the constructed DAG. -/
theorem additions_le_supports : DAGAllocator.additionCount circuit.nodes ≤
    (SharedPointFamily.domain.image SharedPointFamily.support).card :=
  DAGReplayBudget.additions_le_card _ _ supports_nodup additionSupports_subset

/-- The finite support certificate transfers to actual compiled storage. -/
theorem allocated_roles_le
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    (DAGAllocator.compile circuit.nodes outputRefs).state.next ≤ 509194 := by
  have ha := additions_le_supports.trans hcard
  have hr := DAGAllocator.compile_roles_le circuit.nodes outputRefs valid outputRefs_bounds
  rw [outputRefs_count] at hr
  omega

/-- The same certificate bounds every instruction emitted by the allocator. -/
theorem compiled_instructions_le
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    (DAGAllocator.compile circuit.nodes outputRefs).program.length ≤ 959588 := by
  have ha := additions_le_supports.trans hcard
  have hr := DAGAllocator.compile_program_le_additions circuit.nodes outputRefs valid outputRefs_bounds
  rw [outputRefs_count] at hr
  omega

end IntegerMultBounds.Networks.SharedPointReplay
