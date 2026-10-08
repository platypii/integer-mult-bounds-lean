import IntegerMultBounds.Networks.DAGAllocatorCount

/-! The live frontier follows the actual consumer ports: issued by an earlier
node and not yet consumed by a gate. This invariant proves slot allocation
structurally, independently of scalar values or support frames. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

abbrev Wiring := List (ℕ × Port)

def consumers (wires : Wiring) (node : ℕ) : List Port :=
  (wires.filter (fun p => p.1 == node)).map Prod.snd

def Pending (offset : ℕ) : Port → Prop
  | .gate node _ => offset ≤ node
  | .output _ => True

def Domain (wires : Wiring) (offset : ℕ) (state : State) : Prop :=
  ∀ port, port ∈ state.live.map Prod.fst ↔
    (∃ owner, owner < offset ∧ (owner, port) ∈ wires) ∧ Pending offset port

/-- A port's unique producing node is determined by the concrete wire list. -/
structure WiringValid (wires : Wiring) : Prop where
  unique : (wires.map Prod.snd).Nodup
  later : ∀ owner target right, (owner, .gate target right) ∈ wires → owner < target

theorem consumers_mem (wires : Wiring) (node : ℕ) (port : Port) :
    port ∈ consumers wires node ↔ (node,port) ∈ wires := by
  simp only [consumers, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨owner,p⟩, ⟨hp, he⟩, rfl⟩
    have he' : owner = node := by simpa using he
    simpa [he'] using hp
  · intro hp
    exact ⟨(node,port), ⟨hp, by simp⟩, rfl⟩

theorem WiringValid.consumers_nodup {wires : Wiring} (hw : WiringValid wires) (node : ℕ) :
    (consumers wires node).Nodup :=
  hw.unique.sublist (List.filter_sublist.map Prod.snd)

theorem WiringValid.owner_unique {wires : Wiring} (hw : WiringValid wires)
    (left right : ℕ) (port : Port) (hl : (left,port) ∈ wires) (hr : (right,port) ∈ wires) : left = right := by
  have hi := List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.snd hw.unique) |>.mp hw.unique
  exact congrArg Prod.fst (hi _ hl _ hr rfl)

theorem retained_keys (state : State) (index : ℕ) (port : Port) :
    port ∈ (retained state index).map Prod.fst ↔
      port ∈ state.live.map Prod.fst ∧ port ≠ .gate index false ∧ port ≠ .gate index true := by
  simp only [retained, List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
  aesop

/-- New user ports cannot already be pending: every pending port was issued
by a strictly earlier node, and the actual wiring has unique port keys. -/
theorem fresh_consumers (wires : Wiring) (index : ℕ) (state : State)
    (hw : WiringValid wires) (hd : Domain wires index state) :
    (consumers wires index).Disjoint ((retained state index).map Prod.fst) := by
  intro port hp hr
  obtain ⟨owner, ho, how⟩ := ((hd port).mp ((retained_keys state index port).mp hr).1).1
  have he := hw.owner_unique index owner port ((consumers_mem wires index port).mp hp) how
  omega

/-- Consuming the current gate ports and publishing the current node's user
ports advances exactly the mathematically specified frontier domain. -/
theorem allocate_domain {ι : Type*} (wires : Wiring) (index : ℕ) (state : State)
    (node : Node ι) (hw : WiringValid wires) (hd : Domain wires index state)
    (hc : consumers wires index ≠ []) :
    Domain wires (index+1) (allocate state index node (consumers wires index)).state := by
  intro port
  have hlen := allocate_outputs_length state index node (consumers wires index) hc
  have hkeys : ((allocate state index node (consumers wires index)).state.live.map Prod.fst) =
      consumers wires index ++ (retained state index).map Prod.fst := by
    change (((consumers wires index).zip (allocate state index node (consumers wires index)).gate.outputs ++
      retained state index).map Prod.fst) = _
    rw [List.map_append, List.map_fst_zip (by omega)]
  rw [hkeys, List.mem_append, consumers_mem, retained_keys, hd]
  constructor
  · rintro (hnew | ⟨⟨⟨owner, ho, how⟩, hp⟩, h0, h1⟩)
    · refine ⟨⟨index, by omega, hnew⟩, ?_⟩
      cases port with
      | output n => trivial
      | gate target right =>
        have hh := hw.later index target right hnew
        exact hh
    · refine ⟨⟨owner, by omega, how⟩, ?_⟩
      cases port with
      | output n => trivial
      | gate target right =>
        change index ≤ target at hp
        change index+1 ≤ target
        have hne : target ≠ index := by
          intro he
          subst target
          cases right
          · exact h0 rfl
          · exact h1 rfl
        omega
  · rintro ⟨⟨owner, ho, how⟩, hp⟩
    by_cases he : owner = index
    · exact Or.inl (he ▸ how)
    · right
      refine ⟨⟨⟨owner, by omega, how⟩, ?_⟩, ?_, ?_⟩
      · cases port with
        | output n => trivial
        | gate target right => change index+1 ≤ target at hp; exact Nat.le_trans (by omega) hp
      · intro he
        subst port
        change index+1 ≤ index at hp
        omega
      · intro he
        subst port
        change index+1 ≤ index at hp
        omega

/-- The frontier invariant is preserved by the exact transition, with freshness
and key uniqueness discharged from the original wiring domain. -/
theorem allocate_frontier_domain {ι : Type*} (wires : Wiring) (index : ℕ) (state : State)
    (node : Node ι) (hw : WiringValid wires) (hd : Domain wires index state)
    (hf : Frontier state) (hi : InputsReady state index node) (hc : consumers wires index ≠ []) :
    Frontier (allocate state index node (consumers wires index)).state ∧
      Domain wires (index+1) (allocate state index node (consumers wires index)).state :=
  ⟨allocate_frontier state index node _ hc (hw.consumers_nodup index) (fresh_consumers wires index state hw hd) hf hi,
    allocate_domain wires index state node hw hd hc⟩

end IntegerMultBounds.Networks.DAGAllocator
