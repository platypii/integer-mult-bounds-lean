import IntegerMultBounds.Networks.DAGAllocator

/-! Exact role accounting for the executable DAG allocator. Consumer incidence
is counted from the real pruned DAG and requested output list. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

variable {ι : Type*}

def activeCountFrom (active : Finset ℕ) : ℕ → List (Node ι) → ℕ
  | _, [] => 0
  | offset, _ :: nodes => (if offset ∈ active then 1 else 0) + activeCountFrom active (offset+1) nodes

def sourcesFrom (active : Finset ℕ) : ℕ → List (Node ι) → ℕ
  | _, [] => 0
  | offset, node :: nodes => (if offset ∈ active then sourceCount node else 0) + sourcesFrom active (offset+1) nodes

def usesFrom (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ) : ℕ → List (Node ι) → ℕ
  | _, [] => 0
  | offset, _ :: nodes => (if offset ∈ active then (users all active outputs offset).length else 0) +
      usesFrom all active outputs (offset+1) nodes

/-- Accumulating the actual per-node allocations gives the exact role balance. -/
theorem compileFrom_count (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    (compileFrom all active outputs state offset nodes).state.next + activeCountFrom active offset nodes =
      state.next + sourcesFrom active offset nodes + usesFrom all active outputs offset nodes := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom, activeCountFrom, sourcesFrom, usesFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · have ht := ih (allocate state offset node (users all active outputs offset)).state (offset+1)
      have hc := allocate_count state offset node (users all active outputs offset) (hlive offset ha)
      simp only [compileFrom, ha, ↓reduceIte, activeCountFrom, sourcesFrom, usesFrom] at ht ⊢
      omega
    · simpa only [compileFrom, ha, ↓reduceIte, activeCountFrom, sourcesFrom, usesFrom, zero_add] using ih state (offset+1)

theorem sources_additions (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι)) :
    sourcesFrom active offset nodes + DisjointPruning.additionCountFrom offset active nodes =
      activeCountFrom active offset nodes := by
  induction nodes generalizing offset with
  | nil => rfl
  | cons node nodes ih =>
    have hh := ih (offset+1)
    cases node with
    | mk kind support =>
      cases kind <;> simp only [sourcesFrom, DisjointPruning.additionCountFrom, sourceCount, activeCountFrom]
      all_goals split_ifs <;> omega

def indexSum (f : ℕ → ℕ) (offset : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => f offset + indexSum f (offset+1) n

theorem indexSum_add (f g : ℕ → ℕ) (offset n : ℕ) :
    indexSum (fun i => f i + g i) offset n = indexSum f offset n + indexSum g offset n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih => simp [indexSum, ih]; omega

theorem indexSum_indicator (target offset n : ℕ) :
    indexSum (fun i => if target = i then 1 else 0) offset n =
      if offset ≤ target ∧ target < offset+n then 1 else 0 := by
  induction n generalizing offset with
  | zero => simp [indexSum]
  | succ n ih =>
    rw [indexSum, ih]
    split_ifs <;> omega

theorem indexSum_count (owners : List ℕ) (offset n : ℕ) :
    indexSum (fun i => owners.count i) offset n =
      (owners.filter (fun i => decide (offset ≤ i ∧ i < offset+n))).length := by
  induction owners with
  | nil =>
    induction n generalizing offset with
    | zero => rfl
    | succ n ih => simpa [indexSum] using ih (offset+1)
  | cons owner owners ih =>
    have he : (fun i => (owner::owners).count i) =
        (fun i => (if owner = i then 1 else 0) + owners.count i) := by
      funext i
      simp [List.count_cons, beq_iff_eq, Nat.add_comm]
    rw [he, indexSum_add, indexSum_indicator, ih]
    by_cases h : offset ≤ owner ∧ owner < offset+n <;> simp [h, Nat.add_comm]

theorem users_length (nodes : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ) (i : ℕ) :
    (users nodes active outputs i).length =
      ((gatePortsFrom active 0 nodes ++ requestedPorts outputs).map Prod.fst).count i := by
  rw [users, List.length_map, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  rfl

/-- A concrete consumer is owned by an active node whenever the active set is
closed under the actual DAG parent pointers. -/
theorem gatePorts_active (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι))
    (hc : DisjointPruning.ClosedFrom offset active nodes) :
    ∀ p ∈ gatePortsFrom active offset nodes, p.1 ∈ active := by
  induction nodes generalizing offset with
  | nil => simp [gatePortsFrom]
  | cons node nodes ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · by_cases ha : offset ∈ active
      · have hm : p ∈ parentPorts offset node := by simpa [ha] using hp
        exact hc.1 ha ((parentPorts_keys offset node p.1).mp (List.mem_map.mpr ⟨p, hm, rfl⟩))
      · simp [ha] at hp
    · exact ih (offset+1) hc.2 p hp

variable [DecidableEq ι]

theorem gatePorts_bounded (active : Finset ℕ) (prior : List (Finset ι)) (nodes : List (Node ι))
    (hv : ValidFrom prior nodes) :
    ∀ p ∈ gatePortsFrom active prior.length nodes, p.1 < prior.length + nodes.length := by
  induction nodes generalizing prior with
  | nil => simp [gatePortsFrom]
  | cons node nodes ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · by_cases ha : prior.length ∈ active
      · have hm : p ∈ parentPorts prior.length node := by simpa [ha] using hp
        have hh := DisjointPruning.parents_lt prior node hv.1 p.1
          ((parentPorts_keys prior.length node p.1).mp (List.mem_map.mpr ⟨p, hm, rfl⟩))
        simp only [List.length_cons]
        omega
      · simp [ha] at hp
    · have hh := ih (prior ++ [node.support]) hv.2 p
        (by simpa only [List.length_append, List.length_singleton] using hp)
      simp only [List.length_append, List.length_cons, List.length_nil] at hh ⊢
      omega

omit [DecidableEq ι] in
theorem usesFrom_eq_indexSum (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (offset : ℕ) (nodes : List (Node ι))
    (ha : ∀ p ∈ gatePortsFrom active 0 all ++ requestedPorts outputs, p.1 ∈ active) :
    usesFrom all active outputs offset nodes =
      indexSum (fun i => ((gatePortsFrom active 0 all ++ requestedPorts outputs).map Prod.fst).count i)
        offset nodes.length := by
  induction nodes generalizing offset with
  | nil => rfl
  | cons node nodes ih =>
    rw [usesFrom, List.length_cons, indexSum, ih]
    by_cases hi : offset ∈ active
    · rw [ite_eq_left hi, users_length]
    · have hz : ((gatePortsFrom active 0 all ++ requestedPorts outputs).map Prod.fst).count offset = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
        exact hi (he ▸ ha p hp)
      rw [ite_eq_right hi, hz]

omit [DecidableEq ι] in
theorem gatePorts_length (active : Finset ℕ) (offset : ℕ) (nodes : List (Node ι)) :
    (gatePortsFrom active offset nodes).length = 2 * DisjointPruning.additionCountFrom offset active nodes := by
  induction nodes generalizing offset with
  | nil => rfl
  | cons node nodes ih =>
    cases node with
    | mk kind support =>
      cases kind <;> simp only [gatePortsFrom, DisjointPruning.additionCountFrom, List.length_append]
      all_goals split_ifs <;> simp only [parentPorts, List.length_cons, List.length_nil, ih] <;> omega

/-- Every consumer of the marked DAG is owned by an in-bounds active node. -/
theorem marked_consumers (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    let active := DisjointPruning.mark nodes outputs.toFinset
    ∀ p ∈ gatePortsFrom active 0 nodes ++ requestedPorts outputs,
      p.1 ∈ active ∧ p.1 < nodes.length := by
  intro active p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ⟨gatePorts_active active 0 nodes (DisjointPruning.markFrom_closed [] nodes outputs.toFinset hv) p hp,
      by simpa using gatePorts_bounded active [] nodes hv p hp⟩
  · have hm : p.1 ∈ outputs := by
      rw [← requestedPorts_keys outputs]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    exact ⟨DisjointPruning.roots_subset_markFrom 0 nodes outputs.toFinset (List.mem_toFinset.mpr hm), ho p.1 hm⟩

/-- Count each real consumer exactly once at its owner: two ports per active
addition, plus one per requested output, including repeated output nodes. -/
theorem marked_uses_count (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    let active := DisjointPruning.mark nodes outputs.toFinset
    usesFrom nodes active outputs 0 nodes =
      2 * DisjointPruning.additionCountFrom 0 active nodes + outputs.length := by
  intro active
  have hm := marked_consumers nodes outputs hv ho
  rw [usesFrom_eq_indexSum nodes active outputs 0 nodes (fun p hp => (hm p hp).1), indexSum_count]
  have hf : (((gatePortsFrom active 0 nodes ++ requestedPorts outputs).map Prod.fst).filter
      (fun i => decide (0 ≤ i ∧ i < 0+nodes.length))) =
      (gatePortsFrom active 0 nodes ++ requestedPorts outputs).map Prod.fst := by
    apply List.filter_eq_self.mpr
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    simp [(hm p hp).2]
  rw [hf, List.length_map, List.length_append, gatePorts_length]
  simp [requestedPorts]

/-- The literal executable allocator uses exactly one role per active addition
plus one per requested output. Its count is derived from actual backward
pruning and consumer incidence, with no assumed compiler count or checker. -/
theorem compile_roles (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    (compile nodes outputs).state.next =
      DisjointPruning.additionCountFrom 0 (DisjointPruning.mark nodes outputs.toFinset) nodes + outputs.length := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  have hc := compileFrom_count nodes active outputs ⟨0, []⟩ 0 nodes
    (fun i hi => users_mark_nonempty nodes outputs i hi)
  have hs := sources_additions active 0 nodes
  have hu := marked_uses_count nodes outputs hv ho
  change usesFrom nodes active outputs 0 nodes =
    2 * DisjointPruning.additionCountFrom 0 active nodes + outputs.length at hu
  change (compile nodes outputs).state.next + activeCountFrom active 0 nodes =
    0 + sourcesFrom active 0 nodes + usesFrom nodes active outputs 0 nodes at hc
  change (compile nodes outputs).state.next = DisjointPruning.additionCountFrom 0 active nodes + outputs.length
  omega

end IntegerMultBounds.Networks.DAGAllocator
