import IntegerMultBounds.Networks.DisjointPruning
import IntegerMultBounds.Networks.ReversibleFanout
import Mathlib.Data.List.Range

/-! Literal role allocation for a pruned addition DAG. Consumer ports preserve
upstream gate/argument order and requested-output order. Each node shares its
first input slot with its first output, allocates all other outputs fresh,
and retires its nonpivot inputs. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

/-- Gate arguments and requested outputs are separate, concrete consumers. -/
inductive Port where
  | gate (node : ℕ) (right : Bool)
  | output (index : ℕ)
  deriving DecidableEq, Repr

/-- Dependency ports occur in argument order, even when parents coincide. -/
def parentPorts {ι : Type*} (index : ℕ) (node : Node ι) : List (ℕ × Port) :=
  match node.kind with
  | .input _ => []
  | .add left right => [(left, .gate index false), (right, .gate index true)]

/-- Scan active nodes in their actual topological list order. -/
def gatePortsFrom {ι : Type*} (active : Finset ℕ) : ℕ → List (Node ι) → List (ℕ × Port)
  | _, [] => []
  | index, node :: nodes =>
    (if index ∈ active then parentPorts index node else []) ++ gatePortsFrom active (index+1) nodes

def requestedPorts (outputs : List ℕ) : List (ℕ × Port) :=
  outputs.zipIdx.map (fun p => (p.1, .output p.2))

/-- The exact `users[node]` order: active gate uses, then external outputs. -/
def users {ι : Type*} (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ) (node : ℕ) : List Port :=
  ((gatePortsFrom active 0 nodes ++ requestedPorts outputs).filter (fun p => p.1 == node)).map Prod.snd

/-- The actual allocator keeps a frontier of consumer ports and their slots. -/
structure State where
  next : ℕ
  live : List (Port × ℕ)
  deriving Repr

/-- Total association lookup; structural proofs establish presence before use. -/
def slot (live : List (Port × ℕ)) (port : Port) : ℕ :=
  ((live.find? (fun p => p.1 == port)).map Prod.snd).getD 0

structure Gate where
  node : ℕ
  inputs : List ℕ
  outputs : List ℕ
  deriving Repr

structure Step where
  state : State
  gate : Gate
  source : Option ℕ
  deriving Repr

/-- Literal single-node allocation: new source pivot or first incoming port;
second input retired; fresh outputs appended in ascending slot order. -/
def allocate {ι : Type*} (state : State) (index : ℕ) (node : Node ι) (consumers : List Port) : Step :=
  let ins := match node.kind with
    | .input _ => [state.next]
    | .add _ _ => [slot state.live (.gate index false), slot state.live (.gate index true)]
  let seed := match node.kind with | .input _ => state.next + 1 | .add _ _ => state.next
  let outs := ins.headD 0 :: List.range' seed (consumers.length - 1)
  let rest := state.live.filter (fun p => p.1 != .gate index false && p.1 != .gate index true)
  { state := ⟨seed + consumers.length - 1, consumers.zip outs ++ rest⟩
    gate := ⟨index, ins, outs⟩
    source := match node.kind with | .input _ => some state.next | .add _ _ => none }

structure Code where
  state : State
  gates : List Gate
  sources : List (ℕ × ℕ)
  deriving Repr

/-- Run the real allocator over active DAG nodes, preserving allocation order. -/
def compileFrom {ι : Type*} (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) : List (Node ι) → Code
  | [] => ⟨state, [], []⟩
  | node :: nodes =>
    if offset ∈ active then
      let first := allocate state offset node (users all active outputs offset)
      let rest := compileFrom all active outputs first.state (offset+1) nodes
      ⟨rest.state, first.gate :: rest.gates,
        (first.source.toList.map (offset, ·)) ++ rest.sources⟩
    else compileFrom all active outputs state (offset+1) nodes

/-- Roots and pruning are computed from the actual requested output list. -/
def compile {ι : Type*} (nodes : List (Node ι)) (outputs : List ℕ) : Code :=
  let active := DisjointPruning.mark nodes outputs.toFinset
  compileFrom nodes active outputs ⟨0, []⟩ 0 nodes

/-- A frontier is a one-to-one assignment of pending consumer ports to already
allocated slots. Retired slots need not appear in this list. -/
structure Frontier (state : State) : Prop where
  ports : (state.live.map Prod.fst).Nodup
  slots : (state.live.map Prod.snd).Nodup
  bounded : ∀ p ∈ state.live, p.2 < state.next

/-- Number of new source pivots allocated by this node. -/
def sourceCount {ι : Type*} (node : Node ι) : ℕ :=
  match node.kind with | .input _ => 1 | .add _ _ => 0

theorem allocate_inputs_length {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) : (allocate state index node consumers).gate.inputs.length = 2 - sourceCount node := by
  cases node with | mk kind support => cases kind <;> rfl

theorem allocate_outputs_length {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hc : consumers ≠ []) :
    (allocate state index node consumers).gate.outputs.length = consumers.length := by
  have hp := List.length_pos_iff.mpr hc
  cases node with | mk kind support => cases kind <;> simp [allocate] <;> omega

/-- Exact per-node role accounting, with no assumed allocator output count. -/
theorem allocate_count {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hc : consumers ≠ []) :
    (allocate state index node consumers).state.next + 1 = state.next + sourceCount node + consumers.length := by
  have hp := List.length_pos_iff.mpr hc
  cases node with | mk kind support => cases kind <;> simp [allocate, sourceCount] <;> omega

/-- Fresh output slots are exactly the allocated interval, after the pivot. -/
theorem allocate_output_tail {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) :
    (allocate state index node consumers).gate.outputs.tail =
      List.range' (state.next + sourceCount node) (consumers.length - 1) := by
  cases node with | mk kind support => cases kind <;> simp [allocate, sourceCount]

/-- Each concrete input port of an addition is consumed and removed from the
remaining frontier before the node's output assignments are added. -/
theorem retired_absent (state : State) (index : ℕ) (right : Bool) :
    ∀ p ∈ state.live.filter (fun p => p.1 != .gate index false && p.1 != .gate index true),
      p.1 ≠ .gate index right := by
  intro p hp
  have hh := (List.mem_filter.mp hp).2
  have hh' : p.1 ≠ .gate index false ∧ p.1 ≠ .gate index true := by simpa using hh
  cases right
  · exact hh'.1
  · exact hh'.2

/-- Presence concerns the actual frontier keys before allocation. -/
def InputsReady {ι : Type*} (state : State) (index : ℕ) (node : Node ι) : Prop :=
  match node.kind with
  | .input _ => True
  | .add _ _ => .gate index false ∈ state.live.map Prod.fst ∧
      .gate index true ∈ state.live.map Prod.fst

theorem slot_mem (live : List (Port × ℕ)) (port : Port) (hp : port ∈ live.map Prod.fst) :
    (port, slot live port) ∈ live := by
  induction live with
  | nil => simp at hp
  | cons p ps ih =>
    by_cases he : p.1 = port
    · simp [slot, he, Prod.ext_iff]
    · have ht : port ∈ ps.map Prod.fst := by simpa [he, Ne.symm he] using hp
      simpa [slot, he] using List.mem_cons_of_mem p (ih ht)

theorem Frontier.slot_lt {state : State} (hf : Frontier state) (port : Port)
    (hp : port ∈ state.live.map Prod.fst) : slot state.live port < state.next :=
  hf.bounded _ (slot_mem state.live port hp)

theorem Frontier.slot_ne {state : State} (hf : Frontier state) (p q : Port)
    (hp : p ∈ state.live.map Prod.fst) (hq : q ∈ state.live.map Prod.fst) (hne : p ≠ q) :
    slot state.live p ≠ slot state.live q := by
  intro he
  have hinj := List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.snd hf.slots) |>.mp hf.slots
  have hh := hinj _ (slot_mem state.live p hp) _ (slot_mem state.live q hq) he
  exact hne (congrArg Prod.fst hh)

private theorem not_mem_fresh (seed count r : ℕ) (hr : r < seed) : r ∉ List.range' seed count := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.mem_range'.mp hm
  omega

/-- Every actual allocator transition has a concrete reversible fanout layout:
inputs and outputs are each distinct and share exactly their first pivot. -/
theorem allocate_layout {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hf : Frontier state) (hi : InputsReady state index node) :
    ∃ layout : ReversibleFanout.Layout ℕ,
      layout.inputs = (allocate state index node consumers).gate.inputs ∧
      layout.outputs = (allocate state index node consumers).gate.outputs := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      refine ⟨⟨state.next, [], List.range' (state.next+1) (consumers.length-1), by simp,
        List.nodup_range', by simp, not_mem_fresh _ _ _ (by omega), by simp⟩, rfl, rfl⟩
    | add left right =>
      have hp : .gate index false ∈ state.live.map Prod.fst := hi.1
      have hq : .gate index true ∈ state.live.map Prod.fst := hi.2
      have hpl := hf.slot_lt _ hp
      have hql := hf.slot_lt _ hq
      have hpq := hf.slot_ne _ _ hp hq (by simp)
      refine ⟨⟨slot state.live (.gate index false), [slot state.live (.gate index true)],
        List.range' state.next (consumers.length-1), by simp, List.nodup_range', by simpa using hpq,
        not_mem_fresh _ _ _ hpl, ?_⟩, rfl, rfl⟩
      intro r hr hs
      have he : r = slot state.live (.gate index true) := by simpa using hr
      subst r
      exact not_mem_fresh _ _ _ hql hs

/-- The concrete gate's input/output intersection is precisely its pivot. -/
theorem allocate_shared_pivot {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hf : Frontier state) (hi : InputsReady state index node) (slot : ℕ) :
    (slot ∈ (allocate state index node consumers).gate.inputs ∧
      slot ∈ (allocate state index node consumers).gate.outputs) ↔
      slot = (allocate state index node consumers).gate.inputs.headD 0 := by
  obtain ⟨layout, hins, houts⟩ := allocate_layout state index node consumers hf hi
  rw [← hins, ← houts, layout.shared_only_pivot]
  rfl

/-- Increasing the active set only adds consumer ports. -/
theorem gatePortsFrom_mono {ι : Type*} (nodes : List (Node ι)) (offset : ℕ)
    {active larger : Finset ℕ} (he : active ⊆ larger) :
    gatePortsFrom active offset nodes ⊆ gatePortsFrom larger offset nodes := by
  induction nodes generalizing offset with
  | nil => simp [gatePortsFrom]
  | cons node nodes ih =>
    intro p hp
    simp only [gatePortsFrom, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · left
      split_ifs at hp with ha
      · simp only [ite_eq_left (he ha)]
        exact hp
      · simp at hp
    · exact Or.inr (ih (offset+1) hp)

theorem parentPorts_keys {ι : Type*} (index : ℕ) (node : Node ι) (p : ℕ) :
    p ∈ (parentPorts index node).map Prod.fst ↔ p ∈ DisjointPruning.parents node := by
  cases node with | mk kind support => cases kind <;> simp [parentPorts, DisjointPruning.parents]

/-- Every backward-marked node is requested directly or has a concrete active
gate consumer. This derives the upstream `assert users[node]` condition. -/
theorem markFrom_live {ι : Type*} (nodes : List (Node ι)) (offset : ℕ) (roots : Finset ℕ)
    (p : ℕ) (hp : p ∈ DisjointPruning.markFrom offset nodes roots) :
    p ∈ roots ∨ p ∈ (gatePortsFrom (DisjointPruning.markFrom offset nodes roots) offset nodes).map Prod.fst := by
  induction nodes generalizing offset with
  | nil => exact Or.inl hp
  | cons node nodes ih =>
    let marked := DisjointPruning.markFrom (offset+1) nodes roots
    by_cases ha : offset ∈ marked
    · have he : DisjointPruning.markFrom offset (node::nodes) roots = marked ∪ DisjointPruning.parents node := by
        change (if offset ∈ marked then marked ∪ DisjointPruning.parents node else marked) = _
        rw [ite_eq_left ha]
      rw [he] at hp ⊢
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases ih (offset+1) hp with hp | hp
        · exact Or.inl hp
        · right
          obtain ⟨port, hport, hkey⟩ := List.mem_map.mp hp
          apply List.mem_map.mpr
          refine ⟨port, ?_, hkey⟩
          apply List.mem_append_right
          exact gatePortsFrom_mono nodes (offset+1) Finset.subset_union_left hport
      · right
        have hp' := (parentPorts_keys offset node p).mpr hp
        obtain ⟨port, hport, hkey⟩ := List.mem_map.mp hp'
        apply List.mem_map.mpr
        refine ⟨port, ?_, hkey⟩
        simp only [gatePortsFrom, ite_eq_left (Finset.mem_union_left _ ha)]
        exact List.mem_append_left _ hport
    · have he : DisjointPruning.markFrom offset (node::nodes) roots = marked := by
        change (if offset ∈ marked then marked ∪ DisjointPruning.parents node else marked) = _
        rw [ite_eq_right ha]
      rw [he] at hp ⊢
      simpa only [gatePortsFrom, ite_eq_right ha, List.nil_append] using ih (offset+1) hp

theorem requestedPorts_keys (outputs : List ℕ) :
    (requestedPorts outputs).map Prod.fst = outputs := by
  simp [requestedPorts, List.map_map, Function.comp_def]

/-- Actual backward pruning ensures every processed node has an output user. -/
theorem users_mark_nonempty {ι : Type*} (nodes : List (Node ι)) (outputs : List ℕ)
    (p : ℕ) (hp : p ∈ DisjointPruning.mark nodes outputs.toFinset) :
    users nodes (DisjointPruning.mark nodes outputs.toFinset) outputs p ≠ [] := by
  have hm := markFrom_live nodes 0 outputs.toFinset p hp
  have hin : p ∈ (gatePortsFrom (DisjointPruning.mark nodes outputs.toFinset) 0 nodes ++ requestedPorts outputs).map Prod.fst := by
    rcases hm with hm | hm
    · rw [List.map_append, requestedPorts_keys]
      exact List.mem_append_right _ (List.mem_toFinset.mp hm)
    · rw [List.map_append]
      exact List.mem_append_left _ hm
  obtain ⟨entry, he, hk⟩ := List.mem_map.mp hin
  have hm : entry.2 ∈ users nodes (DisjointPruning.mark nodes outputs.toFinset) outputs p := by
    apply List.mem_map.mpr
    exact ⟨entry, List.mem_filter.mpr ⟨he, by simpa using hk⟩, rfl⟩
  intro hz
  rw [hz] at hm
  exact List.not_mem_nil hm

/-- The frontier after consuming this node's input ports and before publishing
its outputs. Old slots remain allocated even when absent from this list. -/
def retained (state : State) (index : ℕ) : List (Port × ℕ) :=
  state.live.filter (fun p => p.1 != .gate index false && p.1 != .gate index true)

theorem Frontier.slot_owner {state : State} (hf : Frontier state) (port : Port)
    (hp : port ∈ state.live.map Prod.fst) (entry : Port × ℕ) (he : entry ∈ state.live)
    (hs : entry.2 = slot state.live port) : entry.1 = port := by
  have hinj := List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.snd hf.slots) |>.mp hf.slots
  exact congrArg Prod.fst (hinj _ he _ (slot_mem state.live port hp) hs)

/-- No output slot aliases a retained frontier slot: the pivot was consumed,
and all other outputs are fresh. -/
theorem allocate_outputs_disjoint_retained {ι : Type*} (state : State) (index : ℕ)
    (node : Node ι) (consumers : List Port) (hf : Frontier state) (hi : InputsReady state index node) :
    (allocate state index node consumers).gate.outputs.Disjoint ((retained state index).map Prod.snd) := by
  intro r hr hs
  obtain ⟨entry, he, her⟩ := List.mem_map.mp hs
  have heold : entry ∈ state.live := (List.mem_filter.mp he).1
  have hbound := hf.bounded entry heold
  have hretired := retired_absent state index false entry he
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change r ∈ state.next :: List.range' (state.next+1) (consumers.length-1) at hr
      rcases List.mem_cons.mp hr with hr | hr
      · omega
      · obtain ⟨k, hk, hkr⟩ := List.mem_range'.mp hr
        omega
    | add left right =>
      change r ∈ slot state.live (.gate index false) :: List.range' state.next (consumers.length-1) at hr
      rcases List.mem_cons.mp hr with hr | hr
      · exact hretired (hf.slot_owner _ hi.1 entry heold (her.trans hr))
      · obtain ⟨k, hk, hkr⟩ := List.mem_range'.mp hr
        omega

/-- Every emitted output points inside the allocator's new role interval. -/
theorem allocate_outputs_bounded {ι : Type*} (state : State) (index : ℕ)
    (node : Node ι) (consumers : List Port) (hc : consumers ≠ [])
    (hf : Frontier state) (hi : InputsReady state index node) :
    ∀ r ∈ (allocate state index node consumers).gate.outputs,
      r < (allocate state index node consumers).state.next := by
  intro r hr
  have hlen := List.length_pos_iff.mpr hc
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change r ∈ state.next :: List.range' (state.next+1) (consumers.length-1) at hr
      change r < state.next+1+consumers.length-1
      rcases List.mem_cons.mp hr with hr | hr
      · omega
      · obtain ⟨k, hk, hkr⟩ := List.mem_range'.mp hr
        omega
    | add left right =>
      change r ∈ slot state.live (.gate index false) :: List.range' state.next (consumers.length-1) at hr
      change r < state.next+consumers.length-1
      have hbound := hf.slot_lt _ hi.1
      rcases List.mem_cons.mp hr with hr | hr
      · omega
      · obtain ⟨k, hk, hkr⟩ := List.mem_range'.mp hr
        omega

/-- One literal transition preserves the frontier's injectivity and slot bounds
when its newly produced consumer ports are distinct and not already pending. -/
theorem allocate_frontier {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hc : consumers ≠ []) (hcn : consumers.Nodup)
    (hnew : consumers.Disjoint ((retained state index).map Prod.fst))
    (hf : Frontier state) (hi : InputsReady state index node) :
    Frontier (allocate state index node consumers).state := by
  let outs := (allocate state index node consumers).gate.outputs
  have hlen : consumers.length = outs.length := (allocate_outputs_length state index node consumers hc).symm
  have hfst : (consumers.zip outs).map Prod.fst = consumers := List.map_fst_zip (by omega)
  have hsnd : (consumers.zip outs).map Prod.snd = outs := List.map_snd_zip (by omega)
  obtain ⟨layout, hins, houts⟩ := allocate_layout state index node consumers hf hi
  have houtn : outs.Nodup := by
    change (allocate state index node consumers).gate.outputs.Nodup
    rw [← houts]
    exact layout.outputs_nodup
  have hrestp : ((retained state index).map Prod.fst).Nodup :=
    hf.ports.sublist (List.filter_sublist.map Prod.fst)
  have hrests : ((retained state index).map Prod.snd).Nodup :=
    hf.slots.sublist (List.filter_sublist.map Prod.snd)
  have hnext : state.next ≤ (allocate state index node consumers).state.next := by
    have he := allocate_count state index node consumers hc
    have hp := List.length_pos_iff.mpr hc
    omega
  constructor
  · change (((consumers.zip outs) ++ retained state index).map Prod.fst).Nodup
    rw [List.map_append, hfst, List.nodup_append]
    exact ⟨hcn, hrestp, fun p hp q hq he => hnew hp (he ▸ hq)⟩
  · change (((consumers.zip outs) ++ retained state index).map Prod.snd).Nodup
    rw [List.map_append, hsnd, List.nodup_append]
    exact ⟨houtn, hrests, fun p hp q hq he =>
      allocate_outputs_disjoint_retained state index node consumers hf hi hp (he ▸ hq)⟩
  · intro p hp
    change p ∈ consumers.zip outs ++ retained state index at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact allocate_outputs_bounded state index node consumers hc hf hi p.2 (List.of_mem_zip hp).2
    · exact (hf.bounded p (List.mem_filter.mp hp).1).trans_le hnext

end IntegerMultBounds.Networks.DAGAllocator
