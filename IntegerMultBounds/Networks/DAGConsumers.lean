import IntegerMultBounds.Networks.DAGAllocatorFrontier

/-! Structural certificates for the literal ordered consumer list. Gate ports
are unique, occur strictly after their producers, and exist for every active
addition input. Output ports remain unique even for repeated requested nodes. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

variable {ι : Type*}

theorem parentPorts_target (index : ℕ) (node : Node ι) (p : ℕ × Port)
    (hp : p ∈ parentPorts index node) : ∃ right, p.2 = .gate index right := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label => simp [parentPorts] at hp
    | add left right =>
      simp only [parentPorts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp

theorem parentPorts_unique (index : ℕ) (node : Node ι) :
    ((parentPorts index node).map Prod.snd).Nodup := by
  cases node with | mk kind support => cases kind <;> simp [parentPorts]

/-- Every gate port names an active target inside this scanned interval. -/
theorem gatePorts_target (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι))
    (p : ℕ × Port) (hp : p ∈ gatePortsFrom active offset nodes) :
    ∃ target right, p.2 = .gate target right ∧ target ∈ active ∧
      offset ≤ target ∧ target < offset + nodes.length := by
  induction nodes generalizing offset with
  | nil => simp [gatePortsFrom] at hp
  | cons node nodes ih =>
    rcases List.mem_append.mp hp with hp | hp
    · by_cases ha : offset ∈ active
      · have hm : p ∈ parentPorts offset node := by simpa [ha] using hp
        obtain ⟨right, hr⟩ := parentPorts_target offset node p hm
        exact ⟨offset, right, hr, ha, by omega, by simp⟩
      · simp [ha] at hp
    · obtain ⟨target, right, he, ha, hlo, hhi⟩ := ih (offset+1) hp
      exact ⟨target, right, he, ha, by omega, by simp only [List.length_cons]; omega⟩

theorem gatePorts_unique (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι)) :
    ((gatePortsFrom active offset nodes).map Prod.snd).Nodup := by
  induction nodes generalizing offset with
  | nil => simp [gatePortsFrom]
  | cons node nodes ih =>
    rw [gatePortsFrom, List.map_append, List.nodup_append]
    refine ⟨?_, ih (offset+1), ?_⟩
    · split_ifs
      · exact parentPorts_unique offset node
      · simp
    · intro p hp q hq he
      by_cases ha : offset ∈ active
      · obtain ⟨entry, hm, rfl⟩ := List.mem_map.mp hp
        have hm' : entry ∈ parentPorts offset node := by simpa [ha] using hm
        obtain ⟨right, hr⟩ := parentPorts_target offset node entry hm'
        obtain ⟨entry', hm', rfl⟩ := List.mem_map.mp hq
        obtain ⟨target, right', ht, _, hlo, _⟩ := gatePorts_target active (offset+1) nodes entry' hm'
        rw [hr, ht] at he
        have := Port.gate.inj he
        omega
      · simp [ha] at hp

theorem requestedPorts_unique (outputs : List ℕ) :
    ((requestedPorts outputs).map Prod.snd).Nodup := by
  have hr : (List.range' 0 outputs.length).Nodup := List.nodup_range'
  have hn := hr.map
    (f := Port.output) (by intro a b h; exact Port.output.inj h)
  simpa only [requestedPorts, List.map_map, ← List.zipIdx_map_snd, Function.comp_def] using hn

theorem requestedPorts_output (outputs : List ℕ) (p : ℕ × Port)
    (hp : p ∈ requestedPorts outputs) : ∃ index, p.2 = .output index := by
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨entry.2, rfl⟩

/-- Keys are globally unique, independent of support validity or pruning. -/
theorem wiring_unique (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ) :
    ((gatePortsFrom active 0 nodes ++ requestedPorts outputs).map Prod.snd).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨gatePorts_unique active 0 nodes, requestedPorts_unique outputs, ?_⟩
  intro p hp q hq he
  obtain ⟨entry, hm, rfl⟩ := List.mem_map.mp hp
  obtain ⟨entry', hm', rfl⟩ := List.mem_map.mp hq
  obtain ⟨target, right, ht, _⟩ := gatePorts_target active 0 nodes entry hm
  obtain ⟨index, hi⟩ := requestedPorts_output outputs entry' hm'
  simp [ht, hi] at he

/-- An active node contributes each of its actual input ports. -/
theorem parentPorts_mem_gatePorts (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι))
    (i : ℕ) (hi : i < nodes.length) (ha : offset+i ∈ active)
    (p : ℕ × Port) (hp : p ∈ parentPorts (offset+i) nodes[i]) :
    p ∈ gatePortsFrom active offset nodes := by
  induction nodes generalizing offset i with
  | nil => simp at hi
  | cons node nodes ih =>
    cases i with
    | zero =>
      apply List.mem_append_left
      have ha' : offset ∈ active := by simpa using ha
      simpa [ha'] using hp
    | succ i =>
      apply List.mem_append_right
      apply ih (offset+1) i (by simpa using hi)
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

variable [DecidableEq ι]

/-- Valid parent pointers always precede their consuming gate. -/
theorem gatePorts_later (active : Finset ℕ) (prior : List (Finset ι)) (nodes : List (Node ι))
    (hv : ValidFrom prior nodes) (owner target : ℕ) (right : Bool)
    (hp : (owner, .gate target right) ∈ gatePortsFrom active prior.length nodes) : owner < target := by
  induction nodes generalizing prior with
  | nil => simp [gatePortsFrom] at hp
  | cons node nodes ih =>
    rcases List.mem_append.mp hp with hp | hp
    · by_cases ha : prior.length ∈ active
      · have hm : (owner, .gate target right) ∈ parentPorts prior.length node := by simpa [ha] using hp
        obtain ⟨side, he⟩ := parentPorts_target prior.length node _ hm
        have ht : target = prior.length := (Port.gate.inj he).1
        rw [ht]
        exact DisjointPruning.parents_lt prior node hv.1 owner
          ((parentPorts_keys prior.length node owner).mp (List.mem_map.mpr ⟨_, hm, rfl⟩))
      · simp [ha] at hp
    · exact ih (prior ++ [node.support]) hv.2
        (by simpa only [List.length_append, List.length_singleton] using hp)

/-- The actual ordered wiring meets the frontier proof's structural premises. -/
theorem wiring_valid (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (hv : Valid nodes) : WiringValid (gatePortsFrom active 0 nodes ++ requestedPorts outputs) := by
  refine ⟨wiring_unique nodes active outputs, ?_⟩
  intro owner target right hp
  rcases List.mem_append.mp hp with hp | hp
  · exact gatePorts_later active [] nodes hv owner target right hp
  · obtain ⟨index, hi⟩ := requestedPorts_output outputs _ hp
    contradiction

/-- Each actual active input port has an earlier owner in the full wiring. -/
theorem active_input_earlier (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (hv : Valid nodes) (index : ℕ) (hi : index < nodes.length) (ha : index ∈ active)
    (port : Port) (hp : port ∈ (parentPorts index nodes[index]).map Prod.snd) :
    ∃ owner, owner < index ∧
      (owner, port) ∈ gatePortsFrom active 0 nodes ++ requestedPorts outputs := by
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hp
  have hm : entry ∈ gatePortsFrom active 0 nodes :=
    parentPorts_mem_gatePorts active 0 nodes index hi (by simpa using ha) entry (by simpa using he)
  have hw : entry ∈ gatePortsFrom active 0 nodes ++ requestedPorts outputs := List.mem_append_left _ hm
  refine ⟨entry.1, ?_, hw⟩
  obtain ⟨right, ht⟩ := parentPorts_target index nodes[index] entry he
  exact (wiring_valid nodes active outputs hv).later entry.1 index right (by rw [← ht]; exact hw)

omit [DecidableEq ι] in
/-- Inactive gates have no argument ports anywhere in the concrete wiring. -/
theorem inactive_no_target (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (index : ℕ) (ha : index ∉ active) (owner : ℕ) (right : Bool) :
    (owner, .gate index right) ∉ gatePortsFrom active 0 nodes ++ requestedPorts outputs := by
  intro hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨target, side, ht, hm, _⟩ := gatePorts_target active 0 nodes _ hp
    have he : index = target := (Port.gate.inj ht).1
    exact ha (he ▸ hm)
  · obtain ⟨target, ht⟩ := requestedPorts_output outputs _ hp
    contradiction

/-- Backward closure ensures an inactive node owns no requested consumer. -/
theorem marked_inactive_no_owner (nodes : List (Node ι)) (outputs : List ℕ)
    (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length)
    (index : ℕ) (ha : index ∉ DisjointPruning.mark nodes outputs.toFinset) (port : Port) :
    (index, port) ∉ gatePortsFrom (DisjointPruning.mark nodes outputs.toFinset) 0 nodes ++
      requestedPorts outputs := by
  intro hp
  exact ha ((marked_consumers nodes outputs hv ho (index,port) hp).1)

end IntegerMultBounds.Networks.DAGAllocator
