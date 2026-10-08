import IntegerMultBounds.Networks.DisjointUnique

/-! Replay a valid source DAG into an existing persistent DAG, renaming its
input atoms and interning every node by its exact lifted support. The returned
reference list remaps actual source node indices to actual target indices. -/

namespace IntegerMultBounds.Networks.DAGReplay

open DisjointCircuit DisjointBuilder

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Translate one literal source instruction using the already imported parent
references. The default only totalizes invalid source indices. -/
def translated (rename : α ↪ β) (refs : List ℕ) (node : Node α) : Node β :=
  ⟨match node.kind with
    | .input label => .input (rename label)
    | .add left right => .add (refs[left]?.getD 0) (refs[right]?.getD 0),
   node.support.map rename⟩

/-- Scan in source topological order, reusing equal supports globally. -/
def replayFrom (rename : α ↪ β) (target : List (Node β)) (refs : List ℕ) :
    List (Node α) → List (Node β) × List ℕ
  | [] => (target, refs)
  | node :: nodes =>
    let next := intern target (translated rename refs node)
    replayFrom rename next.1 (refs ++ [next.2]) nodes

/-- Import a complete DAG; the returned list has one target reference for each
original source node, in the original order. -/
def replay (rename : α ↪ β) (target : List (Node β)) (source : List (Node α)) :=
  replayFrom rename target [] source

/-- Previously imported source supports agree with the target references. -/
def Aligned (rename : α ↪ β) (prior : List (Finset α))
    (target : List (Node β)) (refs : List ℕ) : Prop :=
  refs.length = prior.length ∧ ∀ j (hj : j < prior.length),
    (target.map Node.support)[refs[j]?.getD 0]? = some (prior[j].map rename)

omit [DecidableEq α] in
theorem intern_extends (target : List (Node β)) (node : Node β) :
    Extends target (intern target node).1 := by
  unfold intern
  split
  · exact extends_refl _
  · exact ⟨[node], rfl⟩

omit [DecidableEq α] [DecidableEq β] in
theorem lookup_bound {target : List (Node β)} {index : ℕ} {support : Finset β}
    (h : (target.map Node.support)[index]? = some support) : index < target.length := by
  by_contra hn
  rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hn)] at h
  contradiction

omit [DecidableEq α] [DecidableEq β] in
theorem lookup_extends {target larger : List (Node β)} (he : Extends target larger)
    {index : ℕ} {support : Finset β} (h : (target.map Node.support)[index]? = some support) :
    (larger.map Node.support)[index]? = some support := by
  obtain ⟨tail, rfl⟩ := he
  rw [List.map_append, List.getElem?_append_left (by simpa using lookup_bound h)]
  exact h

omit [DecidableEq α] [DecidableEq β] in
theorem aligned_extends (rename : α ↪ β) {prior : List (Finset α)}
    {target larger : List (Node β)} {refs : List ℕ} (he : Extends target larger)
    (ha : Aligned rename prior target refs) : Aligned rename prior larger refs :=
  ⟨ha.1, fun j hj => lookup_extends he (ha.2 j hj)⟩

/-- A translated source instruction is structurally valid against the actual
current target: source parent references are replaced by already proved refs. -/
theorem translated_valid (rename : α ↪ β) (prior : List (Finset α))
    (target : List (Node β)) (refs : List ℕ) (node : Node α)
    (ha : Aligned rename prior target refs) (hn : node.Valid prior) :
    (translated rename refs node).Valid (target.map Node.support) := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      change support = {label} at hn
      simp [translated, Node.Valid, hn]
    | add left right =>
      simp only [Node.Valid] at hn
      split at hn
      next hl =>
        split at hn
        next hr =>
          have hleft := ha.2 left hl
          have hright := ha.2 right hr
          have hbl := lookup_bound hleft
          have hbr := lookup_bound hright
          have hsl : (target.map Node.support)[refs[left]?.getD 0]'(by simpa using hbl) =
              prior[left].map rename := (List.getElem?_eq_some_iff.mp hleft).2
          have hsr : (target.map Node.support)[refs[right]?.getD 0]'(by simpa using hbr) =
              prior[right].map rename := (List.getElem?_eq_some_iff.mp hright).2
          simp only [translated, Node.Valid, List.length_map,
            hbl, hbr, ↓reduceDIte]
          rw [hsl, hsr, hn.2, Finset.map_union]
          exact ⟨by simpa using hn.1, rfl⟩
        next hr => contradiction
      next hl => contradiction

omit [DecidableEq α] in
/-- Publishing the actual interned reference extends the alignment by one
source support, preserving every previously imported source reference. -/
theorem aligned_step (rename : α ↪ β) (prior : List (Finset α))
    (target : List (Node β)) (refs : List ℕ) (node : Node α)
    (ha : Aligned rename prior target refs) :
    Aligned rename (prior ++ [node.support])
      (intern target (translated rename refs node)).1
      (refs ++ [(intern target (translated rename refs node)).2]) := by
  have hlen := ha.1
  have hold := aligned_extends rename (intern_extends target (translated rename refs node)) ha
  refine ⟨by simp [ha.1], ?_⟩
  intro j hj
  by_cases hlt : j < prior.length
  · rw [List.getElem?_append_left (by omega), List.getElem_append_left hlt]
    exact hold.2 j hlt
  · have he : j = prior.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [List.getElem?_append_right (by omega), List.getElem_append_right (le_refl _)]
    simpa only [← ha.1, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.getElem_cons_zero, translated] using intern_support target (translated rename refs node)

/-- The complete replay preserves validity and all imported support values,
while extending the actual target DAG by a suffix. -/
theorem replayFrom_correct (rename : α ↪ β) (prior : List (Finset α))
    (target : List (Node β)) (refs : List ℕ) (source : List (Node α))
    (ht : Valid target) (hs : ValidFrom prior source) (ha : Aligned rename prior target refs) :
    Valid (replayFrom rename target refs source).1 ∧
      Extends target (replayFrom rename target refs source).1 ∧
      Aligned rename (prior ++ source.map Node.support)
        (replayFrom rename target refs source).1 (replayFrom rename target refs source).2 := by
  induction source generalizing prior target refs with
  | nil => exact ⟨ht, extends_refl _, by simpa [replayFrom] using ha⟩
  | cons node source ih =>
    have hnode := translated_valid rename prior target refs node ha hs.1
    have hstep := aligned_step rename prior target refs node ha
    have hh := ih (prior ++ [node.support])
      (intern target (translated rename refs node)).1
      (refs ++ [(intern target (translated rename refs node)).2])
      (intern_valid target _ ht hnode) hs.2 hstep
    refine ⟨hh.1, extends_trans (intern_extends target _) hh.2.1, ?_⟩
    simpa only [replayFrom, List.map_cons, List.append_assoc, List.singleton_append] using hh.2.2

/-- A complete source DAG imports into any valid target with no assumptions
about uniqueness or overlap between their supports. -/
theorem replay_correct (rename : α ↪ β) (target : List (Node β)) (source : List (Node α))
    (ht : Valid target) (hs : Valid source) :
    Valid (replay rename target source).1 ∧
      Extends target (replay rename target source).1 ∧
      Aligned rename (source.map Node.support)
        (replay rename target source).1 (replay rename target source).2 := by
  have hh := replayFrom_correct rename [] target [] source ht hs ⟨rfl, by simp⟩
  simpa only [replay, List.nil_append] using hh

omit [DecidableEq α] in
/-- All replayed nodes pass through support interning, so global support
uniqueness is maintained even across repeated imports with different renamings. -/
theorem replayFrom_nodup (rename : α ↪ β) (target : List (Node β))
    (refs : List ℕ) (source : List (Node α)) (hn : (target.map Node.support).Nodup) :
    ((replayFrom rename target refs source).1.map Node.support).Nodup := by
  induction source generalizing target refs with
  | nil => exact hn
  | cons node source ih => exact ih _ _ (DisjointUnique.intern_nodup target _ hn)

omit [DecidableEq α] in
theorem replay_nodup (rename : α ↪ β) (target : List (Node β)) (source : List (Node α))
    (hn : (target.map Node.support).Nodup) :
    ((replay rename target source).1.map Node.support).Nodup :=
  replayFrom_nodup rename target [] source hn

/-- Every returned reference is in bounds and denotes the exact lifted support
of its source node. -/
theorem replay_support (rename : α ↪ β) (target : List (Node β)) (source : List (Node α))
    (ht : Valid target) (hs : Valid source) (index : ℕ) (hi : index < source.length) :
    ((replay rename target source).1.map Node.support)[(replay rename target source).2[index]?.getD 0]? = some (source[index].support.map rename) := by
  have hh := (replay_correct rename target source ht hs).2.2.2 index (by simpa using hi)
  change ((replay rename target source).1.map Node.support)[(replay rename target source).2[index]?.getD 0]? =
    some (((source.map Node.support)[index]'(by simpa using hi)).map rename) at hh
  simpa only [List.getElem_map] using hh

/-- Evaluating the imported reference gives exactly the original support sum
under the renamed input valuation. -/
theorem replay_value {A : Type*} [AddCommMonoid A] (rename : α ↪ β)
    (target : List (Node β)) (source : List (Node α)) (input : β → A)
    (ht : Valid target) (hs : Valid source) (index : ℕ) (hi : index < source.length) :
    (eval input (replay rename target source).1)[(replay rename target source).2[index]?.getD 0]? =
      some (supportSum (fun a => input (rename a)) source[index].support) := by
  rw [eval_eq input _ (replay_correct rename target source ht hs).1]
  have hh := congrArg (Option.map (supportSum input))
    (replay_support rename target source ht hs index hi)
  simpa only [← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some,
    supportSum, Finset.sum_map] using hh

/-- Membership in the supports of actual addition records, excluding inputs. -/
def AdditionSupport (nodes : List (Node α)) (support : Finset α) : Prop :=
  ∃ node ∈ nodes, (∃ left right, node.kind = .add left right) ∧ node.support = support

omit [DecidableEq α] [DecidableEq β] in
theorem additionSupport_cons (node : Node α) (nodes : List (Node α)) (support : Finset α) :
    AdditionSupport (node::nodes) support ↔
      ((∃ left right, node.kind = .add left right) ∧ node.support = support) ∨
        AdditionSupport nodes support := by
  constructor
  · rintro ⟨n, hm, hk, hs⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Or.inl ⟨hk, hs⟩
    · exact Or.inr ⟨n, hm, hk, hs⟩
  · rintro (⟨hk, hs⟩ | ⟨n, hm, hk, hs⟩)
    · exact ⟨node, by simp, hk, hs⟩
    · exact ⟨n, by simp [hm], hk, hs⟩

omit [DecidableEq α] in
theorem intern_additionSupport (target : List (Node β)) (node : Node β) (support : Finset β)
    (h : AdditionSupport (intern target node).1 support) :
    AdditionSupport target support ∨
      ((∃ left right, node.kind = .add left right) ∧ node.support = support) := by
  unfold intern at h
  split at h
  · exact Or.inl h
  · obtain ⟨n, hm, hk, hs⟩ := h
    rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl ⟨n, hm, hk, hs⟩
    · have he := List.mem_singleton.mp hm
      subst n
      exact Or.inr ⟨hk, hs⟩

omit [DecidableEq α] [DecidableEq β] in
theorem translated_addition (rename : α ↪ β) (refs : List ℕ) (node : Node α) :
    (∃ left right, (translated rename refs node).kind = .add left right) ↔
      ∃ left right, node.kind = .add left right := by
  cases hk : node.kind <;> simp [translated, hk]

omit [DecidableEq α] in
/-- Every actual replayed addition support comes from an existing target
addition or the injective image of an actual source addition support. -/
theorem replayFrom_additionSupport (rename : α ↪ β) (target : List (Node β))
    (refs : List ℕ) (source : List (Node α)) (support : Finset β)
    (h : AdditionSupport (replayFrom rename target refs source).1 support) :
    AdditionSupport target support ∨
      ∃ localSupport, AdditionSupport source localSupport ∧ localSupport.map rename = support := by
  induction source generalizing target refs with
  | nil => exact Or.inl h
  | cons node source ih =>
    rcases ih (intern target (translated rename refs node)).1
      (refs ++ [(intern target (translated rename refs node)).2]) h with h | h
    · rcases intern_additionSupport target (translated rename refs node) support h with h | ⟨hk, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨node.support,
          ⟨node, by simp, (translated_addition rename refs node).mp hk, rfl⟩, hs⟩
    · obtain ⟨localSupport, ⟨n, hn, hk, hs⟩, he⟩ := h
      exact Or.inr ⟨localSupport, ⟨n, by simp [hn], hk, hs⟩, he⟩

omit [DecidableEq α] in
theorem replay_additionSupport (rename : α ↪ β) (target : List (Node β))
    (source : List (Node α)) (support : Finset β)
    (h : AdditionSupport (replay rename target source).1 support) :
    AdditionSupport target support ∨
      ∃ localSupport, AdditionSupport source localSupport ∧ localSupport.map rename = support :=
  replayFrom_additionSupport rename target [] source support h

omit [DecidableEq α] in
/-- Replay appends one returned target reference per source node, including
nodes whose support is reused rather than allocated. -/
theorem replayFrom_refs_length (rename : α ↪ β) (target : List (Node β))
    (refs : List ℕ) (source : List (Node α)) :
    (replayFrom rename target refs source).2.length = refs.length + source.length := by
  induction source generalizing target refs with
  | nil => simp [replayFrom]
  | cons node source ih =>
      simpa [replayFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (intern target (translated rename refs node)).1
          (refs ++ [(intern target (translated rename refs node)).2])

omit [DecidableEq α] in
theorem replay_refs_length (rename : α ↪ β) (target : List (Node β)) (source : List (Node α)) :
    (replay rename target source).2.length = source.length := by
  simpa [replay] using replayFrom_refs_length rename target [] source

/-- Every concrete returned node identifier is an actual target index. -/
theorem replay_ref_bound (rename : α ↪ β) (target : List (Node β)) (source : List (Node α))
    (ht : Valid target) (hs : Valid source) (index : ℕ) (hi : index < source.length) :
    (replay rename target source).2[index]?.getD 0 < (replay rename target source).1.length :=
  lookup_bound (replay_support rename target source ht hs index hi)

/-- Source evaluation and actual imported-reference evaluation agree, with
input labels renamed injectively into the target alphabet. -/
theorem replay_eval {A : Type*} [AddCommMonoid A] (rename : α ↪ β)
    (target : List (Node β)) (source : List (Node α)) (input : β → A)
    (ht : Valid target) (hs : Valid source) (index : ℕ) (hi : index < source.length) :
    (eval input (replay rename target source).1)[(replay rename target source).2[index]?.getD 0]? =
      (eval (fun a => input (rename a)) source)[index]? := by
  rw [replay_value rename target source input ht hs index hi, eval_eq _ source hs]
  simp [List.getElem?_map, List.getElem?_eq_getElem hi]

end IntegerMultBounds.Networks.DAGReplay
