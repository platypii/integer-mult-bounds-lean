import IntegerMultBounds.Networks.DAGValueTransfer
import IntegerMultBounds.Networks.FanoutFrames

/-! Concrete source-support labels propagated by the literal role allocator.
Each event retains its actual node support and actual allocated gate. Declared
incidences are relabeled together, including identity-node pivots. -/

namespace IntegerMultBounds.Networks.DAGSupportTrace

open DisjointCircuit DAGAllocator
variable {α : Type*} [DecidableEq α]

structure Event (α : Type*) where
  gate : DAGAllocator.Gate
  support : Finset α

def eventFrom (all : List (Node α)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) : List (Node α) → List (Event α)
  | [] => []
  | node :: nodes =>
    if offset ∈ active then
      let step := allocate state offset node (users all active outputs offset)
      ⟨step.gate,node.support⟩ :: eventFrom all active outputs step.state (offset+1) nodes
    else eventFrom all active outputs state (offset+1) nodes

def events (nodes : List (Node α)) (outputs : List ℕ) : List (Event α) :=
  eventFrom nodes (DisjointPruning.mark nodes outputs.toFinset) outputs ⟨0,[]⟩ 0 nodes

omit [DecidableEq α] in
theorem eventFrom_erasure (all : List (Node α)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node α)) :
    (eventFrom all active outputs state offset nodes).map Event.gate =
      (compileFrom all active outputs state offset nodes).gates := by
  induction nodes generalizing state offset with
  | nil => rfl
  | cons node nodes ih =>
    by_cases ha : offset ∈ active <;> simp [eventFrom, compileFrom, ha, ih]

omit [DecidableEq α] in
theorem events_erasure (nodes : List (Node α)) (outputs : List ℕ) :
    (events nodes outputs).map Event.gate = (compile nodes outputs).gates :=
  eventFrom_erasure nodes _ outputs ⟨0,[]⟩ 0 nodes

/-- Source node identifiers distinguish repeated input labels at distinct
physical slots. Union also totalizes an arbitrary, possibly repeated list. -/
def initial (sources : List (ℕ × ℕ)) (value : ℕ → Finset α) (role : ℕ) : Finset α :=
  sources.foldr (fun p rest => if p.2 = role then value p.1 ∪ rest else rest) ∅

@[simp] theorem initial_nil (value : ℕ → Finset α) (role : ℕ) : initial [] value role = ∅ := rfl

@[simp] theorem initial_cons (node source : ℕ) (later : List (ℕ × ℕ))
    (value : ℕ → Finset α) (role : ℕ) :
    initial ((node,source)::later) value role =
      if source = role then value node ∪ initial later value role else initial later value role := rfl

theorem initial_below (sources : List (ℕ × ℕ)) (value : ℕ → Finset α) (bound role : ℕ)
    (hs : ∀ p ∈ sources, bound ≤ p.2) (hr : role < bound) : initial sources value role = ∅ := by
  induction sources with
  | nil => rfl
  | cons p sources ih =>
    have hp := hs p (by simp)
    have ht := ih (fun p hp => hs p (by simp [hp]))
    change (if p.2 = role then value p.1 ∪ initial sources value role else initial sources value role) = ∅
    rw [ite_eq_right (by omega), ht]

/-- Apply exactly the declared-incidence alignment used by FanoutFrames. -/
def Event.after (event : Event α) (current : ℕ → Finset α) (role : ℕ) : Finset α :=
  if role ∈ event.gate.inputs ++ event.gate.outputs then event.support else current role

/-- The local FanoutFrames support premises, before an actual emitted event. -/
def Event.Ready (event : Event α) (current : ℕ → Finset α) : Prop :=
  (∀ r ∈ event.gate.inputs, current r ⊆ event.support) ∧
    ∀ r ∈ event.gate.outputs.tail, current r = ∅

def run : List (Event α) → (ℕ → Finset α) → ℕ → Finset α
  | [], current => current
  | event::rest, current => run rest (event.after current)

def TraceReady : List (Event α) → (ℕ → Finset α) → Prop
  | [], _ => True
  | event::rest, current => event.Ready current ∧ TraceReady rest (event.after current)

def Assigned (wires : Wiring) (state : State) (value current : ℕ → Finset α) : Prop :=
  ∀ entry ∈ state.live, ∀ owner, (owner,entry.1) ∈ wires → current entry.2 = value owner

def Future (state : State) (sources : List (ℕ × ℕ)) (value current : ℕ → Finset α) : Prop :=
  ∀ role, state.next ≤ role → current role = initial sources value role

/-- Source preloading supplies the current input and leaves actual fresh output
roles empty, even though all later source supports are already initialized. -/
theorem initial_step (state : State) (index : ℕ) (node : Node α)
    (cs : List Port) (hc : cs ≠ []) (later : List (ℕ × ℕ)) (value current : ℕ → Finset α)
    (hlater : ∀ p ∈ later, (allocate state index node cs).state.next ≤ p.2)
    (hfuture : Future state
      (((allocate state index node cs).source.toList.map (index, ·)) ++ later) value current) :
    (sourceCount node = 1 → current state.next = value index) ∧
    (∀ r ∈ (allocate state index node cs).gate.outputs.tail, current r = ∅) ∧
    ∀ r, (allocate state index node cs).state.next ≤ r →
      initial (((allocate state index node cs).source.toList.map (index, ·)) ++ later) value r =
        initial later value r := by
  have hlen := List.length_pos_iff.mpr hc
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change Future state ((index,state.next)::later) value current at hfuture
      have hp : state.next < (allocate state index ⟨.input label,support⟩ cs).state.next := by
        change state.next < state.next+1+cs.length-1
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro _
        rw [hfuture state.next (le_refl _), initial_cons, ite_eq_left rfl,
          initial_below later value _ _ hlater hp, Finset.union_empty]
      · intro r hr
        change r ∈ List.range' (state.next+1) (cs.length-1) at hr
        obtain ⟨k, hk, he⟩ := List.mem_range'.mp hr
        have hrange : r < (allocate state index ⟨.input label,support⟩ cs).state.next := by
          change r < state.next+1+cs.length-1
          omega
        rw [hfuture r (by omega), initial_cons, ite_eq_right (by omega),
          initial_below later value _ _ hlater hrange]
      · intro r hr
        change initial ((index,state.next)::later) value r = _
        rw [initial_cons, ite_eq_right (by omega)]
    | add left right =>
      change Future state later value current at hfuture
      refine ⟨by simp [sourceCount], ?_, fun _ _ => rfl⟩
      intro r hr
      change r ∈ List.range' state.next (cs.length-1) at hr
      obtain ⟨k, hk, he⟩ := List.mem_range'.mp hr
      have hrange : r < (allocate state index ⟨.add left right,support⟩ cs).state.next := by
        change r < state.next+cs.length-1
        omega
      rw [hfuture r (by omega), initial_below later value _ _ hlater hrange]

omit [DecidableEq α] in
/-- Frontier ownership identifies the actual input supports with their source
parents, whose supports are contained in the current original DAG support. -/
theorem allocation_inputs (wires : Wiring) (state : State) (index : ℕ) (node : Node α)
    (cs : List Port) (value current : ℕ → Finset α) (hi : InputsReady state index node)
    (ha : Assigned wires state value current) (hn : value index = node.support)
    (hp : ∀ p ∈ parentPorts index node, p ∈ wires ∧ value p.1 ⊆ node.support)
    (hsource : sourceCount node = 1 → current state.next = value index) :
    ∀ r ∈ (allocate state index node cs).gate.inputs, current r ⊆ node.support := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      intro r hr
      have he : r = state.next := by simpa [allocate] using hr
      rw [he, hsource rfl, hn]
    | add left right =>
      have hl := hp (left,.gate index false) (by simp [parentPorts])
      have hr := hp (right,.gate index true) (by simp [parentPorts])
      have hleft := ha _ (slot_mem state.live (.gate index false) hi.1) left hl.1
      have hright := ha _ (slot_mem state.live (.gate index true) hi.2) right hr.1
      intro r hm
      have hm' : r = slot state.live (.gate index false) ∨ r = slot state.live (.gate index true) := by
        simpa [allocate] using hm
      rcases hm' with rfl | rfl
      · rw [hleft]; exact hl.2
      · rw [hright]; exact hr.2

omit [DecidableEq α] in
/-- Relabeling actual declared incidences publishes exact support labels and
preserves all retained frontier labels. -/
theorem allocation_assigned (wires : Wiring) (state : State) (index : ℕ) (node : Node α)
    (value current : ℕ → Finset α) (hw : WiringValid wires) (hf : Frontier state)
    (hi : InputsReady state index node) (ha : Assigned wires state value current)
    (hn : value index = node.support) :
    Assigned wires (allocate state index node (consumers wires index)).state value
      ((⟨(allocate state index node (consumers wires index)).gate,node.support⟩ : Event α).after current) := by
  let step := allocate state index node (consumers wires index)
  intro entry he owner howner
  change entry ∈ (consumers wires index).zip step.gate.outputs ++ retained state index at he
  rcases List.mem_append.mp he with he | he
  · have hpair := List.of_mem_zip he
    have hnew := (consumers_mem wires index entry.1).mp hpair.1
    have hown := hw.owner_unique index owner entry.1 hnew howner
    rw [← hown, hn]
    exact ite_eq_left (List.mem_append_right _ hpair.2)
  · have hold := ha entry (List.mem_filter.mp he).1 owner howner
    have hretained : entry.2 ∈ (retained state index).map Prod.snd := List.mem_map.mpr ⟨entry,he,rfl⟩
    have hnot : entry.2 ∉ step.gate.inputs ++ step.gate.outputs := by
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact DAGValueTransfer.inputs_disjoint_retained state index node _ hf hi hm hretained
      · exact allocate_outputs_disjoint_retained state index node _ hf hi hm hretained
    exact (ite_eq_right hnot).trans hold

/-- Readiness and both inductive invariants propagate through an actual
allocator step, with fresh-role conditions derived from physical allocation. -/
theorem allocation_supports (wires : Wiring) (state : State) (index : ℕ) (node : Node α)
    (later : List (ℕ × ℕ)) (value current : ℕ → Finset α) (hw : WiringValid wires)
    (hf : Frontier state) (hi : InputsReady state index node)
    (hc : consumers wires index ≠ []) (ha : Assigned wires state value current)
    (hn : value index = node.support)
    (hp : ∀ p ∈ parentPorts index node, p ∈ wires ∧ value p.1 ⊆ node.support)
    (hlater : ∀ p ∈ later, (allocate state index node (consumers wires index)).state.next ≤ p.2)
    (hfuture : Future state
      (((allocate state index node (consumers wires index)).source.toList.map (index, ·)) ++ later) value current) :
    let step := allocate state index node (consumers wires index)
    let event : Event α := ⟨step.gate,node.support⟩
    event.Ready current ∧ Assigned wires step.state value (event.after current) ∧
      Future step.state later value (event.after current) := by
  have hinit := initial_step state index node (consumers wires index) hc later value current hlater hfuture
  refine ⟨⟨allocation_inputs wires state index node _ value current hi ha hn hp hinit.1, hinit.2.1⟩,
    allocation_assigned wires state index node value current hw hf hi ha hn, ?_⟩
  intro r hr
  have hnot : r ∉ (allocate state index node (consumers wires index)).gate.inputs ++
      (allocate state index node (consumers wires index)).gate.outputs := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · have hb := allocate_inputs_bounded state index node _ hc hf hi r hm
      omega
    · have hb := allocate_outputs_bounded state index node _ hc hf hi r hm
      omega
  have hnext : state.next ≤ (allocate state index node (consumers wires index)).state.next := by
    have he := allocate_count state index node _ hc
    have hh := List.length_pos_iff.mpr hc
    omega
  rw [Event.after, ite_eq_right hnot, hfuture r (hnext.trans hr), hinit.2.2 r hr]

/-- Original-DAG semantic premises for a suffix, independent of allocation. -/
def SupportsFrom (wires : Wiring) (active : Finset ℕ) (value : ℕ → Finset α) :
    ℕ → List (Node α) → Prop
  | _, [] => True
  | index, node :: nodes =>
    (index ∈ active → value index = node.support ∧
      ∀ p ∈ parentPorts index node, p ∈ wires ∧ value p.1 ⊆ node.support) ∧
      SupportsFrom wires active value (index+1) nodes

/-- Every event in the actual emitted sequence satisfies local framing
readiness, and its declared-incidence updates preserve exact frontier support. -/
theorem eventFrom_ready (all : List (Node α)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node α)) (value current : ℕ → Finset α)
    (hw : WiringValid (gatePortsFrom active 0 all ++ requestedPorts outputs))
    (hs : ScheduledFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active offset nodes)
    (hlive : ∀ i ∈ active, users all active outputs i ≠ [])
    (hv : SupportsFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active value offset nodes)
    (hf : Frontier state) (hd : Domain (gatePortsFrom active 0 all ++ requestedPorts outputs) offset state)
    (ha : Assigned (gatePortsFrom active 0 all ++ requestedPorts outputs) state value current)
    (hfuture : Future state (compileFrom all active outputs state offset nodes).sources value current) :
    let es := eventFrom all active outputs state offset nodes
    let code := compileFrom all active outputs state offset nodes
    TraceReady es current ∧
      Assigned (gatePortsFrom active 0 all ++ requestedPorts outputs) code.state value (run es current) ∧
      Future code.state [] value (run es current) := by
  induction nodes generalizing state offset current with
  | nil => exact ⟨trivial,ha,hfuture⟩
  | cons node nodes ih =>
    by_cases hactive : offset ∈ active
    · obtain ⟨hearly,husers⟩ := hs.1 hactive
      have hin := inputsReady_domain _ state offset node hd hearly
      have hstruct := allocate_frontier_domain _ offset state node hw hd hf hin husers
      let step := allocate state offset node (users all active outputs offset)
      let rest := compileFrom all active outputs step.state (offset+1) nodes
      have hvalues := allocation_supports _ state offset node rest.sources value current hw hf hin husers
        ha (hv.1 hactive).1 (hv.1 hactive).2
        (DAGValueTransfer.sources_lower all active outputs step.state (offset+1) nodes hlive)
        (by simpa only [compileFrom, hactive, ↓reduceIte, rest, step, users, consumers] using hfuture)
      have ht := ih step.state (offset+1) ((⟨step.gate,node.support⟩ : Event α).after current)
        hs.2.2 hv.2 hstruct.1 hstruct.2 hvalues.2.1 hvalues.2.2
      exact ⟨by simpa only [eventFrom, hactive, ↓reduceIte, TraceReady, step, users, consumers] using And.intro hvalues.1 ht.1,
        by simpa only [eventFrom, compileFrom, hactive, ↓reduceIte, run] using ht.2⟩
    · have ht := ih state (offset+1) current hs.2.2 hv.2 hf
        (skip_domain _ state offset hd (hs.2.1 hactive)) ha
        (by simpa only [compileFrom, hactive, ↓reduceIte] using hfuture)
      simpa only [eventFrom, compileFrom, hactive, ↓reduceIte] using ht

/-- Actual semantic support of a node, with empty support only for an invalid
index. All source entries and live parent uses are proved in bounds. -/
def nodeSupport (nodes : List (Node α)) (index : ℕ) : Finset α :=
  (nodes.map Node.support)[index]?.getD ∅

omit [DecidableEq α] in
theorem nodeSupport_get (nodes : List (Node α)) (index : ℕ) (hi : index < nodes.length) :
    nodeSupport nodes index = nodes[index].support := by
  simp [nodeSupport, List.getElem?_map, List.getElem?_eq_getElem hi]

/-- Original validity supplies support inclusion for each actual parent port. -/
theorem nodeSupport_parent (nodes : List (Node α)) (hv : Valid nodes) (index : ℕ)
    (hi : index < nodes.length) (p : ℕ × Port) (hp : p ∈ parentPorts index nodes[index]) :
    nodeSupport nodes p.1 ⊆ nodes[index].support := by
  have hn : nodes[index].Valid ((nodes.take index).map Node.support) := by
    simpa using DAGValueTransfer.validFrom_get [] nodes hv index hi
  cases hk : nodes[index].kind with
  | input label => simp [parentPorts, hk] at hp
  | add left right =>
    simp only [Node.Valid, hk, List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hi)] at hn
    split at hn
    next hl =>
      split at hn
      next hr =>
        simp only [List.getElem_map, List.getElem_take] at hn
        have hm : p = (left,.gate index false) ∨ p = (right,.gate index true) := by
          simpa [parentPorts, hk] using hp
        rcases hm with rfl | rfl
        · rw [nodeSupport_get nodes left (hl.trans hi), hn.2]
          exact Finset.subset_union_left
        · rw [nodeSupport_get nodes right (hr.trans hi), hn.2]
          exact Finset.subset_union_right
      next hr => contradiction
    next hl => contradiction

theorem actual_supportsFrom (nodes : List (Node α)) (active : Finset ℕ) (outputs : List ℕ)
    (hv : Valid nodes) :
    SupportsFrom (gatePortsFrom active 0 nodes ++ requestedPorts outputs) active (nodeSupport nodes) 0 nodes := by
  let wires := gatePortsFrom active 0 nodes ++ requestedPorts outputs
  have suffixes : ∀ (suffix before : List (Node α)), nodes = before ++ suffix →
      SupportsFrom wires active (nodeSupport nodes) before.length suffix := by
    intro suffix
    induction suffix with
    | nil => intro before he; trivial
    | cons node suffix ih =>
      intro before he
      refine ⟨?_, ?_⟩
      · intro ha
        have hi : before.length < nodes.length := by simp [he]
        have hnode : nodes[before.length] = node := by simp [he]
        refine ⟨by simpa only [hnode] using nodeSupport_get nodes before.length hi, ?_⟩
        intro p hp
        constructor
        · apply List.mem_append_left
          apply parentPorts_mem_gatePorts active 0 nodes before.length hi (by simpa using ha) p
          simpa only [Nat.zero_add, hnode] using hp
        · have hh := nodeSupport_parent nodes hv before.length hi p (by simpa only [hnode] using hp)
          simpa only [hnode] using hh
      · have ht := ih (before++[node]) (by simpa [List.append_assoc] using he)
        simpa only [List.length_append, List.length_singleton] using ht
  exact suffixes nodes [] (by simp)

/-- The initial label bank is defined from actual compiler source entries and
actual source node supports; every other physical role starts empty. -/
def initialSupports (nodes : List (Node α)) (outputs : List ℕ) : ℕ → Finset α :=
  initial (compile nodes outputs).sources (nodeSupport nodes)

/-- Global readiness of the actual allocated event sequence: the local framing
premises are derived from DAG validity and requested-output bounds. -/
theorem events_ready (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    TraceReady (events nodes outputs) (initialSupports nodes outputs) ∧
      Assigned (gatePortsFrom (DisjointPruning.mark nodes outputs.toFinset) 0 nodes ++ requestedPorts outputs)
        (compile nodes outputs).state (nodeSupport nodes)
        (run (events nodes outputs) (initialSupports nodes outputs)) := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  have hf : Frontier ⟨0,[]⟩ := ⟨by simp,by simp,by simp⟩
  have hd : Domain (gatePortsFrom active 0 nodes ++ requestedPorts outputs) 0 ⟨0,[]⟩ := by
    intro port; simp
  have ha : Assigned (gatePortsFrom active 0 nodes ++ requestedPorts outputs) ⟨0,[]⟩
      (nodeSupport nodes) (initialSupports nodes outputs) := by intro entry he; simp at he
  have hh := eventFrom_ready nodes active outputs ⟨0,[]⟩ 0 nodes (nodeSupport nodes)
    (initialSupports nodes outputs) (wiring_valid nodes active outputs hv)
    (marked_scheduled nodes outputs hv ho) (fun i hi => users_mark_nonempty nodes outputs i hi)
    (actual_supportsFrom nodes active outputs hv) hf hd ha (fun _ _ => rfl)
  exact ⟨hh.1,hh.2.1⟩

/-- The completed support trace labels every actual requested-output slot by
its exact original node support, not merely an overapproximation. -/
theorem output_support (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (index : ℕ) (hi : index < outputs.length) :
    run (events nodes outputs) (initialSupports nodes outputs) ((compile nodes outputs).outputSlot index) =
      nodeSupport nodes outputs[index] :=
  (events_ready nodes outputs hv ho).2 _
    (slot_mem (compile nodes outputs).state.live (.output index)
      (compile_output_present nodes outputs hv ho index hi)) outputs[index]
    (List.mem_append_right _ (requestedPort_mem outputs index hi))

theorem initial_off_sources (sources : List (ℕ × ℕ)) (value : ℕ → Finset α) (role : ℕ)
    (hr : role ∉ sources.map Prod.snd) : initial sources value role = ∅ := by
  induction sources with
  | nil => rfl
  | cons p sources ih =>
    have hn : p.2 ≠ role := by intro he; exact hr (by simp [he])
    have ht : role ∉ sources.map Prod.snd := fun hm => hr (by simp [hm])
    rw [initial_cons, ite_eq_right hn, ih ht]

theorem initial_at_source (sources : List (ℕ × ℕ)) (value : ℕ → Finset α)
    (hn : (sources.map Prod.snd).Nodup) (entry : ℕ × ℕ) (he : entry ∈ sources) :
    initial sources value entry.2 = value entry.1 := by
  induction sources with
  | nil => simp at he
  | cons first rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp he with rfl | he
    · rw [initial_cons, ite_eq_left rfl, initial_off_sources rest value entry.2 hnot, Finset.union_empty]
    · have hne : first.2 ≠ entry.2 := by
        intro hh
        exact hnot (hh ▸ List.mem_map.mpr ⟨entry, he, rfl⟩)
      rw [initial_cons, ite_eq_right hne]
      exact ih hrest he

/-- Each concrete source slot starts with precisely its original node support;
repeated semantic input labels do not merge physical source locations. -/
theorem initialSupports_source (nodes : List (Node α)) (outputs : List ℕ) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) :
    initialSupports nodes outputs entry.2 = nodeSupport nodes entry.1 :=
  initial_at_source _ _ (DAGValueTransfer.compile_sources_nodup nodes outputs) entry he

theorem initialSupports_other (nodes : List (Node α)) (outputs : List ℕ) (role : ℕ)
    (hr : role ∉ (compile nodes outputs).sources.map Prod.snd) :
    initialSupports nodes outputs role = ∅ := initial_off_sources _ _ role hr

/-- Every erased gate in the emitted support trace has the already proved
actual allocator layout; no layout checker is supplied by a caller. -/
theorem events_layout (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (event : Event α) (he : event ∈ events nodes outputs) :
    event.gate.HasLayout := by
  apply (compile_frontier nodes outputs hv ho).2.2 event.gate
  rw [← events_erasure]
  exact List.mem_map.mpr ⟨event,he,rfl⟩

omit [DecidableEq α] in
/-- Every event retains the support of an actual node in its scanned suffix. -/
theorem eventFrom_support (all : List (Node α)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node α)) (event : Event α)
    (he : event ∈ eventFrom all active outputs state offset nodes) :
    ∃ node ∈ nodes, event.support = node.support := by
  induction nodes generalizing state offset with
  | nil => simp [eventFrom] at he
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · simp only [eventFrom,ha,↓reduceIte,List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨node,by simp,rfl⟩
      · obtain ⟨n,hn,hs⟩ := ih _ _ he
        exact ⟨n,by simp [hn],hs⟩
    · simp only [eventFrom,ha,↓reduceIte] at he
      obtain ⟨n,hn,hs⟩ := ih _ _ he
      exact ⟨n,by simp [hn],hs⟩

omit [DecidableEq α] in
theorem events_support (nodes : List (Node α)) (outputs : List ℕ) (event : Event α)
    (he : event ∈ events nodes outputs) : ∃ node ∈ nodes, event.support = node.support :=
  eventFrom_support nodes _ outputs ⟨0,[]⟩ 0 nodes event he

section Frames
variable {h : ℕ}

/-- Exact declared-incidence span updates for an event's unchanged scalar gate. -/
def Event.updates (event : Event α) (triples : α → Finset (Fin h)) :
    List (ℕ × Submodule ℚ (Fin h → ℚ)) :=
  (event.gate.inputs ++ event.gate.outputs).map fun i => (i,FanoutFrames.label triples event.support)

/-- Concatenate the actual event alignments in allocator execution order. -/
def updates (es : List (Event α)) (triples : α → Finset (Fin h)) :
    List (ℕ × Submodule ℚ (Fin h → ℚ)) := es.flatMap (fun event => event.updates triples)

omit [DecidableEq α] in
/-- The support update is exactly the span-label trace update, so readiness
propagation concerns the labels left by the physical local frame alignment. -/
theorem Event.after_labels (event : Event α) (triples : α → Finset (Fin h))
    (current : ℕ → Finset α) :
    (fun i => FanoutFrames.label triples (event.after current i)) =
      RankTrace.finish (fun i => FanoutFrames.label triples (current i)) (event.updates triples) := by
  funext i
  rw [Event.updates, RankTrace.finish_align]
  by_cases hi : i ∈ event.gate.inputs ++ event.gate.outputs <;> simp [Event.after,hi]

omit [DecidableEq α] in
theorem run_labels (es : List (Event α)) (triples : α → Finset (Fin h)) (current : ℕ → Finset α) :
    (fun i => FanoutFrames.label triples (run es current i)) =
      RankTrace.finish (fun i => FanoutFrames.label triples (current i)) (updates es triples) := by
  induction es generalizing current with
  | nil => rfl
  | cons event es ih =>
    simp only [run, updates, List.flatMap_cons, RankTrace.finish_append]
    rw [ih, event.after_labels]
    rfl

omit [DecidableEq α] in
theorem Event.edges_increasing (event : Event α) (triples : α → Finset (Fin h))
    (current : ℕ → Finset α) (hl : event.gate.HasLayout) (hr : event.Ready current) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (event.updates triples),
      p.1 ≤ p.2 := by
  obtain ⟨layout, hi, ho⟩ := hl
  have hin : ∀ i ∈ layout.inputs, current i ⊆ event.support := by simpa only [hi] using hr.1
  have hout : ∀ i ∈ layout.outputTail, current i = ∅ := by
    have he : layout.outputTail = event.gate.outputs.tail := by rw [← ho]; rfl
    simpa only [he] using hr.2
  simpa only [Event.updates, FanoutFrames.updates, hi, ho] using
    FanoutFrames.edges_increasing layout triples current event.support hin hout

omit [DecidableEq α] in
/-- Actual sequential span-label edges increase throughout the complete trace;
each event starts from exactly the supports left by previous events. -/
theorem trace_increasing (es : List (Event α)) (triples : α → Finset (Fin h))
    (current : ℕ → Finset α) (hl : ∀ event ∈ es, event.gate.HasLayout) (hr : TraceReady es current) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (updates es triples),
      p.1 ≤ p.2 := by
  induction es generalizing current with
  | nil => simp [updates,RankTrace.edges]
  | cons event es ih =>
    intro p hp
    simp only [updates,List.flatMap_cons,RankTrace.edges_append,List.mem_append] at hp
    rcases hp with hp | hp
    · exact event.edges_increasing triples current (hl event (by simp)) hr.1 p hp
    · apply ih (event.after current) (fun event he => hl event (by simp [he])) hr.2 p
      rw [event.after_labels]
      exact hp

/-- Validity and bounds alone discharge global monotonicity of the actual
compiler's source-span trace. No comparability hypotheses are assumed. -/
theorem events_increasing (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h)) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (initialSupports nodes outputs i))
      (updates (events nodes outputs) triples), p.1 ≤ p.2 :=
  trace_increasing _ triples _ (events_layout nodes outputs hv ho) (events_ready nodes outputs hv ho).1

/-- The complete actual compiled forward support trace has zero dimension loss;
this statement does not include later sink attachments or inverse schedules. -/
theorem events_loss_zero (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h)) :
    RankTrace.loss (fun U : Submodule ℚ (Fin h → ℚ) => Module.finrank ℚ U)
      (fun i => FanoutFrames.label triples (initialSupports nodes outputs i))
      (updates (events nodes outputs) triples) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hvalue
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (events_increasing nodes outputs hv ho triples p hp))

omit [DecidableEq α] in
/-- Event readiness and a common point of its actual source support discharge
nondegeneracy of both endpoints of each executed frame edge. -/
theorem Event.edges_nondegenerate (event : Event α) (triples : α → Finset (Fin h))
    (current : ℕ → Finset α) (hl : event.gate.HasLayout) (hr : event.Ready current)
    (common : Fin h) (ht : ∀ a ∈ event.support, (triples a).card = 3)
    (hc : ∀ a ∈ event.support, common ∈ triples a) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (event.updates triples),
      ((Labels.rational h).restrict p.1).Nondegenerate ∧
      ((Labels.rational h).restrict p.2).Nondegenerate := by
  obtain ⟨layout, hi, ho⟩ := hl
  have hin : ∀ i ∈ layout.inputs, current i ⊆ event.support := by simpa only [hi] using hr.1
  have hout : ∀ i ∈ layout.outputTail, current i = ∅ := by
    have he : layout.outputTail = event.gate.outputs.tail := by rw [← ho]; rfl
    simpa only [he] using hr.2
  simpa only [Event.updates, FanoutFrames.updates, hi, ho] using
    FanoutFrames.edges_nondegenerate layout triples current event.support common hin hout ht hc

omit [DecidableEq α] in
theorem trace_nondegenerate (es : List (Event α)) (triples : α → Finset (Fin h))
    (current : ℕ → Finset α) (hl : ∀ event ∈ es, event.gate.HasLayout) (hr : TraceReady es current)
    (hs : ∀ event ∈ es, ∃ common : Fin h,
      ∀ a ∈ event.support, (triples a).card = 3 ∧ common ∈ triples a) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (current i)) (updates es triples),
      ((Labels.rational h).restrict p.1).Nondegenerate ∧
      ((Labels.rational h).restrict p.2).Nondegenerate := by
  induction es generalizing current with
  | nil => simp [updates,RankTrace.edges]
  | cons event es ih =>
    intro p hp
    simp only [updates,List.flatMap_cons,RankTrace.edges_append,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨common,hcommon⟩ := hs event (by simp)
      exact event.edges_nondegenerate triples current (hl event (by simp)) hr.1 common
        (fun a ha => (hcommon a ha).1) (fun a ha => (hcommon a ha).2) p hp
    · apply ih (event.after current) (fun event he => hl event (by simp [he])) hr.2
        (fun event he => hs event (by simp [he])) p
      rw [event.after_labels]
      exact hp

/-- Original node supports with a common point give nondegenerate rational
labels on every actual forward edge. The common point may vary by node. -/
theorem events_nondegenerate (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h))
    (hs : ∀ node ∈ nodes, ∃ common : Fin h,
      ∀ a ∈ node.support, (triples a).card = 3 ∧ common ∈ triples a) :
    ∀ p ∈ RankTrace.edges (fun i => FanoutFrames.label triples (initialSupports nodes outputs i))
      (updates (events nodes outputs) triples),
      ((Labels.rational h).restrict p.1).Nondegenerate ∧
      ((Labels.rational h).restrict p.2).Nondegenerate := by
  apply trace_nondegenerate _ triples _ (events_layout nodes outputs hv ho) (events_ready nodes outputs hv ho).1
  intro event he
  obtain ⟨node,hn,heq⟩ := events_support nodes outputs event he
  simpa only [heq] using hs node hn

end Frames
end IntegerMultBounds.Networks.DAGSupportTrace
