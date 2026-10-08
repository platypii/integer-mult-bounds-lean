import IntegerMultBounds.Networks.DAGCompileCorrect

/-! Value transfer through the actual role allocator. Initial values are placed
at its concrete source roles using source node identifiers, so repeated input
labels do not identify distinct physical source slots. -/

namespace IntegerMultBounds.Networks.DAGValueTransfer

open DisjointCircuit DAGAllocator

/-- Preload precisely the concrete compiler's source roles. All other roles
are zero; node identifiers distinguish physical sources with repeated labels. -/
def initial (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (role : ℕ) : ZMod 2 :=
  ((sources.filter (fun p => p.2 == role)).map (fun p => value p.1)).sum

@[simp] theorem initial_nil (value : ℕ → ZMod 2) (role : ℕ) : initial [] value role = 0 := rfl

theorem initial_append (left right : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (role : ℕ) :
    initial (left ++ right) value role = initial left value role + initial right value role := by
  simp [initial]

theorem initial_below (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (bound role : ℕ)
    (hs : ∀ p ∈ sources, bound ≤ p.2) (hr : role < bound) : initial sources value role = 0 := by
  have he : sources.filter (fun p => p.2 == role) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hb := hs p hp
    simp only [beq_iff_eq]
    omega
  simp [initial, he]

/-- No source in a suffix uses a role allocated before that suffix starts. -/
theorem sources_lower {ι : Type*} (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    ∀ p ∈ (compileFrom all active outputs state offset nodes).sources, state.next ≤ p.2 := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · intro p hp
      simp only [compileFrom, ha, ↓reduceIte] at hp
      rcases List.mem_append.mp hp with hp | hp
      · cases node with
        | mk kind support =>
          cases kind <;> simp [allocate] at hp
          next label => subst p; exact le_refl _
      · have ht := ih (allocate state offset node (users all active outputs offset)).state (offset+1) p hp
        have hc := allocate_count state offset node (users all active outputs offset) (hlive offset ha)
        have hn := List.length_pos_iff.mpr (hlive offset ha)
        omega
    · simpa only [compileFrom, ha, ↓reduceIte] using ih state (offset+1)

/-- Pending physical slots hold exactly their producing DAG node values. -/
def Assigned (wires : Wiring) (state : State) (value : ℕ → ZMod 2) (register : ℕ → ZMod 2) : Prop :=
  ∀ entry ∈ state.live, ∀ owner, (owner,entry.1) ∈ wires → register entry.2 = value owner

/-- Unallocated roles retain precisely the future source initialization. -/
def Future (state : State) (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2)
    (register : ℕ → ZMod 2) : Prop :=
  ∀ role, state.next ≤ role → register role = initial sources value role

/-- The graph value assigned to an addition agrees with its two original
parents. Source node values are independently supplied by initialization. -/
def NodeValue {ι : Type*} (value : ℕ → ZMod 2) (index : ℕ) (node : Node ι) : Prop :=
  match node.kind with | .input _ => True | .add left right => value index = value left + value right

/-- Retained frontier slots lie outside the current gate's input incidence. -/
theorem inputs_disjoint_retained {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (cs : List Port) (hf : Frontier state) (hi : InputsReady state index node) :
    (allocate state index node cs).gate.inputs.Disjoint ((retained state index).map Prod.snd) := by
  intro r hr hs
  obtain ⟨entry, he, her⟩ := List.mem_map.mp hs
  have heold : entry ∈ state.live := (List.mem_filter.mp he).1
  have hbound := hf.bounded entry heold
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      have hh : r = state.next := by simpa [allocate] using hr
      omega
    | add left right =>
      have hm : r = slot state.live (.gate index false) ∨ r = slot state.live (.gate index true) := by
        simpa [allocate] using hr
      rcases hm with hm | hm
      · exact retired_absent state index false entry he (hf.slot_owner _ hi.1 entry heold (her.trans hm))
      · exact retired_absent state index true entry he (hf.slot_owner _ hi.2 entry heold (her.trans hm))

/-- The actual gather inputs sum to the current DAG value. -/
theorem allocation_inputSum {ι : Type*} (wires : Wiring) (state : State) (index : ℕ) (node : Node ι)
    (cs : List Port) (value register : ℕ → ZMod 2) (hi : InputsReady state index node)
    (ha : Assigned wires state value register) (hn : NodeValue value index node)
    (hw : ∀ p ∈ parentPorts index node, p ∈ wires)
    (hsource : sourceCount node = 1 → register state.next = value index) :
    ((allocate state index node cs).gate.inputs.map register).sum = value index := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label => simpa [allocate] using hsource rfl
    | add left right =>
      have hl := ha _ (slot_mem state.live (.gate index false) hi.1) left
        (hw (left,.gate index false) (by simp [parentPorts]))
      have hr := ha _ (slot_mem state.live (.gate index true) hi.2) right
        (hw (right,.gate index true) (by simp [parentPorts]))
      simpa [allocate, hl, hr] using hn.symm

theorem initial_cons (node source : ℕ) (later : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (role : ℕ) :
    initial ((node,source)::later) value role =
      (if source = role then value node else 0) + initial later value role := by
  by_cases he : source = role <;> simp [initial, he]

/-- Future initialization supplies the current source pivot, leaves the fresh
fanout outputs zero, and agrees with the remaining source bank above this step. -/
theorem initial_step {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (cs : List Port) (hc : cs ≠ []) (later : List (ℕ × ℕ)) (value register : ℕ → ZMod 2)
    (hlater : ∀ p ∈ later, (allocate state index node cs).state.next ≤ p.2)
    (hfuture : Future state
      (((allocate state index node cs).source.toList.map (index, ·)) ++ later) value register) :
    (sourceCount node = 1 → register state.next = value index) ∧
    (∀ r ∈ (allocate state index node cs).gate.outputs.tail, register r = 0) ∧
    ∀ r, (allocate state index node cs).state.next ≤ r →
      initial (((allocate state index node cs).source.toList.map (index, ·)) ++ later) value r =
        initial later value r := by
  have hlen := List.length_pos_iff.mpr hc
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change Future state ((index,state.next)::later) value register at hfuture
      have hp : state.next < (allocate state index ⟨.input label,support⟩ cs).state.next := by
        change state.next < state.next+1+cs.length-1
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro _
        rw [hfuture state.next (le_refl _), initial_cons, ite_eq_left rfl,
          initial_below later value _ _ hlater hp, add_zero]
      · intro r hr
        change r ∈ List.range' (state.next+1) (cs.length-1) at hr
        obtain ⟨k, hk, he⟩ := List.mem_range'.mp hr
        have hrange : r < (allocate state index ⟨.input label,support⟩ cs).state.next := by
          change r < state.next+1+cs.length-1
          omega
        rw [hfuture r (by omega), initial_cons, ite_eq_right (by omega),
          initial_below later value _ _ hlater hrange, zero_add]
      · intro r hr
        change initial ((index,state.next)::later) value r = _
        rw [initial_cons, ite_eq_right (by omega), zero_add]
    | add left right =>
      change Future state later value register at hfuture
      refine ⟨by simp [sourceCount], ?_, fun _ _ => rfl⟩
      intro r hr
      change r ∈ List.range' state.next (cs.length-1) at hr
      obtain ⟨k, hk, he⟩ := List.mem_range'.mp hr
      have hrange : r < (allocate state index ⟨.add left right,support⟩ cs).state.next := by
        change r < state.next+cs.length-1
        omega
      rw [hfuture r (by omega), initial_below later value _ _ hlater hrange]

/-- A real allocated step preserves all not-yet-allocated roles. -/
theorem allocation_preserves_above {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (cs : List Port) (hc : cs ≠ []) (hf : Frontier state) (hi : InputsReady state index node)
    (register : ℕ → ZMod 2) (r : ℕ) (hr : (allocate state index node cs).state.next ≤ r) :
    Circuit.run (allocate state index node cs).gate.program register r = register r := by
  obtain ⟨layout, hins, houts⟩ := allocate_layout state index node cs hf hi
  rw [Gate.program_eq_layout _ layout hins houts]
  apply layout.outside_preserved
  · intro hm
    rw [hins] at hm
    have hh := allocate_inputs_bounded state index node cs hc hf hi r hm
    omega
  · intro hm
    rw [houts] at hm
    have hh := allocate_outputs_bounded state index node cs hc hf hi r hm
    omega

/-- Exact values of the real published and retained frontier roles after one
physical gather/scatter step. -/
theorem allocation_assigned {ι : Type*} (wires : Wiring) (state : State) (index : ℕ) (node : Node ι)
    (value register : ℕ → ZMod 2) (hw : WiringValid wires) (hf : Frontier state)
    (hi : InputsReady state index node) (ha : Assigned wires state value register)
    (hn : NodeValue value index node) (hp : ∀ p ∈ parentPorts index node, p ∈ wires)
    (hsource : sourceCount node = 1 → register state.next = value index)
    (hfresh : ∀ r ∈ (allocate state index node (consumers wires index)).gate.outputs.tail, register r = 0) :
    Assigned wires (allocate state index node (consumers wires index)).state value
      (Circuit.run (allocate state index node (consumers wires index)).gate.program register) := by
  let step := allocate state index node (consumers wires index)
  obtain ⟨layout, hins, houts⟩ := allocate_layout state index node (consumers wires index) hf hi
  have hsum := allocation_inputSum wires state index node (consumers wires index) value register hi ha hn hp hsource
  have houtputs (r : ℕ) (hr : r ∈ step.gate.outputs) :
      Circuit.run step.gate.program register r = value index := by
    rw [Gate.program_eq_layout _ layout hins houts]
    have ht := layout.fresh_outputs register (fun r hr => hfresh r (by
      rw [← houts]
      exact hr)) r (houts ▸ hr)
    change Circuit.run layout.program register r = _ at ht
    rw [ReversibleFanout.Layout.inputSum, hins] at ht
    exact ht.trans hsum
  intro entry he owner howner
  change entry ∈ (consumers wires index).zip step.gate.outputs ++ retained state index at he
  rcases List.mem_append.mp he with he | he
  · have hpair := List.of_mem_zip he
    have hnew := (consumers_mem wires index entry.1).mp hpair.1
    have hown := hw.owner_unique index owner entry.1 hnew howner
    rw [← hown]
    exact houtputs entry.2 hpair.2
  · have hold := ha entry (List.mem_filter.mp he).1 owner howner
    have hretained : entry.2 ∈ (retained state index).map Prod.snd := List.mem_map.mpr ⟨entry,he,rfl⟩
    rw [Gate.program_eq_layout _ layout hins houts]
    have heq := layout.outside_preserved register entry.2
      (fun hm => inputs_disjoint_retained state index node (consumers wires index) hf hi (hins ▸ hm) hretained)
      (fun hm => allocate_outputs_disjoint_retained state index node (consumers wires index) hf hi (houts ▸ hm) hretained)
    exact heq.trans hold

/-- Source preloading, fresh-output zeros, and the frontier node values all
propagate through the actual allocation transition. -/
theorem allocation_values {ι : Type*} (wires : Wiring) (state : State) (index : ℕ) (node : Node ι)
    (later : List (ℕ × ℕ)) (value register : ℕ → ZMod 2) (hw : WiringValid wires)
    (hf : Frontier state) (hi : InputsReady state index node)
    (hc : consumers wires index ≠ []) (ha : Assigned wires state value register)
    (hn : NodeValue value index node) (hp : ∀ p ∈ parentPorts index node, p ∈ wires)
    (hlater : ∀ p ∈ later, (allocate state index node (consumers wires index)).state.next ≤ p.2)
    (hfuture : Future state
      (((allocate state index node (consumers wires index)).source.toList.map (index, ·)) ++ later) value register) :
    let step := allocate state index node (consumers wires index)
    let next := Circuit.run step.gate.program register
    Assigned wires step.state value next ∧ Future step.state later value next := by
  have hinit := initial_step state index node (consumers wires index) hc later value register hlater hfuture
  refine ⟨allocation_assigned wires state index node value register hw hf hi ha hn hp hinit.1 hinit.2.1, ?_⟩
  intro r hr
  rw [allocation_preserves_above state index node _ hc hf hi register r hr]
  have hnext : state.next ≤ (allocate state index node (consumers wires index)).state.next := by
    have he := allocate_count state index node _ hc
    have hh := List.length_pos_iff.mpr hc
    omega
  rw [hfuture r (hnext.trans hr), hinit.2.2 r hr]

/-- Semantic premises for the original node list, before allocation. -/
def ValuesFrom {ι : Type*} (wires : Wiring) (active : Finset ℕ) (value : ℕ → ZMod 2) :
    ℕ → List (Node ι) → Prop
  | _, [] => True
  | index, node :: nodes =>
    (index ∈ active → NodeValue value index node ∧ ∀ p ∈ parentPorts index node, p ∈ wires) ∧
      ValuesFrom wires active value (index+1) nodes

/-- Execution of the actual compiled suffix transports all live DAG values
and preserves the preloaded future-source invariant. -/
theorem compileFrom_values {ι : Type*} (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι)) (value register : ℕ → ZMod 2)
    (hw : WiringValid (gatePortsFrom active 0 all ++ requestedPorts outputs))
    (hs : ScheduledFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active offset nodes)
    (hlive : ∀ i ∈ active, users all active outputs i ≠ [])
    (hv : ValuesFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active value offset nodes)
    (hf : Frontier state) (hd : Domain (gatePortsFrom active 0 all ++ requestedPorts outputs) offset state)
    (ha : Assigned (gatePortsFrom active 0 all ++ requestedPorts outputs) state value register)
    (hfuture : Future state (compileFrom all active outputs state offset nodes).sources value register) :
    let code := compileFrom all active outputs state offset nodes
    let final := Circuit.run code.program register
    Assigned (gatePortsFrom active 0 all ++ requestedPorts outputs) code.state value final ∧
      Future code.state [] value final := by
  induction nodes generalizing state offset register with
  | nil => exact ⟨ha,hfuture⟩
  | cons node nodes ih =>
    by_cases hactive : offset ∈ active
    · obtain ⟨hearly,husers⟩ := hs.1 hactive
      have hin := inputsReady_domain _ state offset node hd hearly
      have hstruct := allocate_frontier_domain _ offset state node hw hd hf hin husers
      let step := allocate state offset node (users all active outputs offset)
      let rest := compileFrom all active outputs step.state (offset+1) nodes
      have hvalues := allocation_values _ state offset node rest.sources value register hw hf hin husers
        ha (hv.1 hactive).1 (hv.1 hactive).2
        (sources_lower all active outputs step.state (offset+1) nodes hlive)
        (by simpa only [compileFrom, hactive, ↓reduceIte, rest, step, users, consumers] using hfuture)
      have ht := ih step.state (offset+1) (Circuit.run step.gate.program register)
        hs.2.2 hv.2 hstruct.1 hstruct.2 hvalues.1 hvalues.2
      simpa only [compileFrom, hactive, ↓reduceIte, Code.program, List.flatMap_cons, Circuit.run_append] using ht
    · have ht := ih state (offset+1) register hs.2.2 hv.2 hf
        (skip_domain _ state offset hd (hs.2.1 hactive)) ha
        (by simpa only [compileFrom, hactive, ↓reduceIte] using hfuture)
      simpa only [compileFrom, hactive, ↓reduceIte] using ht

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual DAG supplies the semantic schedule once its node values obey
the actual addition equations. -/
theorem actual_valuesFrom (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (value : ℕ → ZMod 2) (hvalue : ∀ i (hi : i < nodes.length), NodeValue value i nodes[i]) :
    ValuesFrom (gatePortsFrom active 0 nodes ++ requestedPorts outputs) active value 0 nodes := by
  let wires := gatePortsFrom active 0 nodes ++ requestedPorts outputs
  have suffixes : ∀ (suffix before : List (Node ι)), nodes = before ++ suffix →
      ValuesFrom wires active value before.length suffix := by
    intro suffix
    induction suffix with
    | nil => intro before he; trivial
    | cons node suffix ih =>
      intro before he
      refine ⟨?_, ?_⟩
      · intro ha
        have hi : before.length < nodes.length := by simp [he]
        have hnode : nodes[before.length] = node := by simp [he]
        refine ⟨by simpa only [hnode] using hvalue before.length hi, ?_⟩
        intro p hp
        apply List.mem_append_left
        apply parentPorts_mem_gatePorts active 0 nodes before.length hi (by simpa using ha) p
        simpa only [Nat.zero_add, hnode] using hp
      · have ht := ih (before++[node]) (by simpa [List.append_assoc] using he)
        simpa only [List.length_append, List.length_singleton] using ht
  exact suffixes nodes [] (by simp)

/-- Main-bank value transfer for the actual allocator and scalar program.
Node values obey only the original DAG equations; the theorem derives all
allocation layouts, source availability, and zero freshness internally. -/
theorem compile_output_value (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (value : ℕ → ZMod 2)
    (hvalue : ∀ i (hi : i < nodes.length), NodeValue value i nodes[i])
    (index : ℕ) (hi : index < outputs.length) :
    Circuit.run (compile nodes outputs).program (initial (compile nodes outputs).sources value)
      ((compile nodes outputs).outputSlot index) = value outputs[index] := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  have hf : Frontier ⟨0,[]⟩ := ⟨by simp,by simp,by simp⟩
  have hd : Domain (gatePortsFrom active 0 nodes ++ requestedPorts outputs) 0 ⟨0,[]⟩ := by intro port; simp
  have ha : Assigned (gatePortsFrom active 0 nodes ++ requestedPorts outputs) ⟨0,[]⟩ value
      (initial (compile nodes outputs).sources value) := by intro entry he; simp at he
  have hh := compileFrom_values nodes active outputs ⟨0,[]⟩ 0 nodes value
    (initial (compile nodes outputs).sources value) (wiring_valid nodes active outputs hv)
    (marked_scheduled nodes outputs hv ho) (fun i hi => users_mark_nonempty nodes outputs i hi)
    (actual_valuesFrom nodes active outputs value hvalue) hf hd ha (fun _ _ => rfl)
  exact hh.1 _ (slot_mem (compile nodes outputs).state.live (.output index)
    (compile_output_present nodes outputs hv ho index hi)) outputs[index]
    (List.mem_append_right _ (requestedPort_mem outputs index hi))

/-- Canonical node values are the certified support sums of the original DAG. -/
def nodeValues (nodes : List (Node ι)) (input : ι → ZMod 2) (index : ℕ) : ZMod 2 :=
  ((nodes.map (fun node => supportSum input node.support))[index]?).getD 0

omit [DecidableEq ι] in
theorem nodeValues_get (nodes : List (Node ι)) (input : ι → ZMod 2) (index : ℕ) (hi : index < nodes.length) :
    nodeValues nodes input index = supportSum input nodes[index].support := by
  simp [nodeValues, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem validFrom_get (prior : List (Finset ι)) (nodes : List (Node ι))
    (hv : ValidFrom prior nodes) (i : ℕ) (hi : i < nodes.length) :
    nodes[i].Valid (prior ++ (nodes.take i).map Node.support) := by
  induction nodes generalizing prior i with
  | nil => simp at hi
  | cons node nodes ih =>
    cases i with
    | zero => simpa using hv.1
    | succ i =>
      have hh := ih (prior ++ [node.support]) hv.2 i (by simpa using hi)
      simpa [List.take_succ_cons, List.append_assoc] using hh

omit [DecidableEq ι] in
theorem nodeValues_take (nodes : List (Node ι)) (input : ι → ZMod 2) (bound index : ℕ)
    (hi : index < bound) :
    (((nodes.take bound).map (fun node => supportSum input node.support))[index]?).getD 0 =
      nodeValues nodes input index := by
  rw [List.map_take, List.getElem?_take_of_lt hi]
  rfl

/-- The verified DAG semantics discharge every node addition equation used by
the physical value-transfer invariant. -/
theorem nodeValues_consistent (nodes : List (Node ι)) (input : ι → ZMod 2) (hv : Valid nodes)
    (index : ℕ) (hi : index < nodes.length) : NodeValue (nodeValues nodes input) index nodes[index] := by
  have hn : nodes[index].Valid ((nodes.take index).map Node.support) := by
    simpa using validFrom_get [] nodes hv index hi
  cases hkind : nodes[index].kind with
  | input label => simp [NodeValue, hkind]
  | add left right =>
    have hl := DisjointPruning.parents_lt _ _ hn left (by simp [DisjointPruning.parents, hkind])
    have hr := DisjointPruning.parents_lt _ _ hn right (by simp [DisjointPruning.parents, hkind])
    simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hl hr
    have he := Node.eval_eq input ((nodes.take index).map Node.support) nodes[index] hn
    simp only [Node.eval, hkind, List.map_map, Function.comp_def] at he
    rw [nodeValues_take nodes input index left hl, nodeValues_take nodes input index right hr] at he
    simpa only [NodeValue, hkind, nodeValues_get nodes input index hi] using he.symm

/-- The actual compiled scalar program produces the original DAG's certified
support sum at every concrete requested output slot. -/
theorem compile_support_value (nodes : List (Node ι)) (outputs : List ℕ) (input : ι → ZMod 2)
    (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length)
    (index : ℕ) (hi : index < outputs.length) :
    Circuit.run (compile nodes outputs).program
      (initial (compile nodes outputs).sources (nodeValues nodes input))
      ((compile nodes outputs).outputSlot index) =
      supportSum input (nodes[outputs[index]]'(ho _ (List.getElem_mem hi))).support := by
  rw [compile_output_value nodes outputs hv ho (nodeValues nodes input)
    (nodeValues_consistent nodes input hv) index hi]
  exact nodeValues_get nodes input outputs[index] (ho _ (List.getElem_mem hi))

omit [DecidableEq ι] in
/-- Concrete source entries come only from actual input nodes in the scanned
DAG, retaining the node index even when input labels repeat. -/
theorem compileFrom_source_mem (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι)) (entry : ℕ × ℕ)
    (he : entry ∈ (compileFrom all active outputs state offset nodes).sources) :
    ∃ j, ∃ hj : j < nodes.length, ∃ label, entry.1 = offset + j ∧ nodes[j].kind = .input label := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom] at he
  | cons node nodes ih =>
    have tail (state' : State)
        (ht : entry ∈ (compileFrom all active outputs state' (offset+1) nodes).sources) :
        ∃ j, ∃ hj : j < (node::nodes).length, ∃ label,
          entry.1 = offset + j ∧ (node::nodes)[j].kind = .input label := by
      obtain ⟨j, hj, label, hindex, hkind⟩ := ih state' (offset+1) ht
      exact ⟨j+1, by simpa using hj, label, by omega, by simpa using hkind⟩
    by_cases ha : offset ∈ active
    · simp only [compileFrom, ha, ↓reduceIte] at he
      rcases List.mem_append.mp he with he | he
      · cases hk : node.kind with
        | input label =>
          have hp : entry = (offset,state.next) := by simpa [allocate, hk] using he
          exact ⟨0, by simp, label, by simp [hp], by simpa using hk⟩
        | add left right => simp [allocate, hk] at he
      · exact tail _ he
    · simp only [compileFrom, ha, ↓reduceIte] at he
      exact tail _ he

/-- Source initialization reads the actual input label at a concrete DAG node.
Additions and out-of-range indices have zero source value. -/
def sourceInput (nodes : List (Node ι)) (input : ι → ZMod 2) (index : ℕ) : ZMod 2 :=
  match nodes[index]? with
  | some node => match node.kind with | .input label => input label | .add _ _ => 0
  | none => 0

theorem sourceInput_eq_nodeValues (nodes : List (Node ι)) (outputs : List ℕ)
    (input : ι → ZMod 2) (hv : Valid nodes) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) :
    sourceInput nodes input entry.1 = nodeValues nodes input entry.1 := by
  obtain ⟨j, hj, label, hindex, hkind⟩ := compileFrom_source_mem nodes
    (DisjointPruning.mark nodes outputs.toFinset) outputs ⟨0,[]⟩ 0 nodes entry he
  simp only [Nat.zero_add] at hindex
  have hn := validFrom_get [] nodes hv j hj
  have hs : nodes[j].support = {label} := by simpa [Node.Valid, hkind] using hn
  rw [hindex, nodeValues_get nodes input j hj]
  simp [sourceInput, List.getElem?_eq_getElem hj, hkind, hs, supportSum]

omit [DecidableEq ι] in
theorem initial_congr (sources : List (ℕ × ℕ)) (left right : ℕ → ZMod 2)
    (h : ∀ entry ∈ sources, left entry.1 = right entry.1) :
    initial sources left = initial sources right := by
  funext role
  unfold initial
  congr 1
  apply List.map_congr_left
  intro entry he
  exact h entry (List.mem_filter.mp he).1

/-- End-to-end scalar value transfer: initialize the actual compiler's source
slots from their actual input labels, leave other roles zero, and execute its
literal gather/scatter program to obtain each certified DAG support sum. -/
theorem compile_output_input_value (nodes : List (Node ι)) (outputs : List ℕ)
    (input : ι → ZMod 2) (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length)
    (index : ℕ) (hi : index < outputs.length) :
    Circuit.run (compile nodes outputs).program
      (initial (compile nodes outputs).sources (sourceInput nodes input))
      ((compile nodes outputs).outputSlot index) =
      supportSum input (nodes[outputs[index]]'(ho _ (List.getElem_mem hi))).support := by
  rw [initial_congr _ _ _ (sourceInput_eq_nodeValues nodes outputs input hv)]
  exact compile_support_value nodes outputs input hv ho index hi

omit [DecidableEq ι] in
/-- Allocated source roles are pairwise distinct, independently of whether
semantic input labels repeat. -/
theorem compileFrom_sources_nodup (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    ((compileFrom all active outputs state offset nodes).sources.map Prod.snd).Nodup := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · simp only [compileFrom, ha, ↓reduceIte, List.map_append]
      cases hk : node.kind with
      | add left right =>
          simpa [allocate, hk] using ih (allocate state offset node (users all active outputs offset)).state (offset+1)
      | input label =>
        have ht := ih (allocate state offset node (users all active outputs offset)).state (offset+1)
        have hl := sources_lower all active outputs
          (allocate state offset node (users all active outputs offset)).state (offset+1) nodes hlive
        have hp := List.length_pos_iff.mpr (hlive offset ha)
        have hn : state.next ∉
            ((compileFrom all active outputs
              (allocate state offset node (users all active outputs offset)).state
              (offset+1) nodes).sources.map Prod.snd) := by
          intro hm
          obtain ⟨entry, he, hrole⟩ := List.mem_map.mp hm
          have hh := hl entry he
          simp only [allocate, hk] at hh
          omega
        simpa [allocate, hk] using List.nodup_cons.mpr ⟨hn, ht⟩
    · simpa only [compileFrom, ha, ↓reduceIte] using ih state (offset+1)

omit [DecidableEq ι] in
theorem compile_sources_nodup (nodes : List (Node ι)) (outputs : List ℕ) :
    ((compile nodes outputs).sources.map Prod.snd).Nodup :=
  compileFrom_sources_nodup nodes (DisjointPruning.mark nodes outputs.toFinset) outputs
    ⟨0,[]⟩ 0 nodes (fun i hi => users_mark_nonempty nodes outputs i hi)

theorem initial_off_sources (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (role : ℕ)
    (hr : role ∉ sources.map Prod.snd) : initial sources value role = 0 := by
  have hf : sources.filter (fun p => p.2 == role) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry he
    simp only [beq_iff_eq]
    intro hh
    exact hr (List.mem_map.mpr ⟨entry, he, hh⟩)
  simp [initial, hf]

theorem initial_at_source (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2)
    (hn : (sources.map Prod.snd).Nodup) (entry : ℕ × ℕ) (he : entry ∈ sources) :
    initial sources value entry.2 = value entry.1 := by
  induction sources with
  | nil => simp at he
  | cons first rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp he with rfl | he
    · rw [initial_cons, ite_eq_left rfl, initial_off_sources rest value entry.2 hnot, add_zero]
    · have hne : first.2 ≠ entry.2 := by
        intro hh
        exact hnot (hh ▸ List.mem_map.mpr ⟨entry, he, rfl⟩)
      rw [initial_cons, ite_eq_right hne, zero_add]
      exact ih hrest he

end IntegerMultBounds.Networks.DAGValueTransfer
