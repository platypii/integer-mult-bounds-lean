import IntegerMultBounds.Networks.DisjointCircuit

/-! Executable cancellation-free DAG construction with absent references
representing zero. Smart addition elides zeros and interns actual union
supports. List totals execute these constructors recursively; all node-count
bounds concern constructed DAG nodes, not tape runtime. -/

namespace IntegerMultBounds.Networks.DisjointBuilder

open DisjointCircuit

variable {ι A : Type*} [DecidableEq ι]

abbrev Ref := Option ℕ
abbrev Result (ι : Type*) := List (Node ι) × Ref

def RefValid (nodes : List (Node ι)) : Ref → Prop
  | none => True
  | some i => i < nodes.length

def refSupport (nodes : List (Node ι)) : Ref → Finset ι
  | none => ∅
  | some i => (nodes.map Node.support)[i]?.getD ∅

omit [DecidableEq ι] in
theorem refSupport_some (nodes : List (Node ι)) (i : ℕ) (hi : i < nodes.length) :
    refSupport nodes (some i) = nodes[i].support := by
  simp only [refSupport, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

def Extends (nodes larger : List (Node ι)) : Prop := ∃ tail, larger = nodes ++ tail

omit [DecidableEq ι] in
theorem extends_refl (nodes : List (Node ι)) : Extends nodes nodes := ⟨[], by simp⟩

omit [DecidableEq ι] in
theorem extends_trans {nodes middle larger : List (Node ι)}
    (hm : Extends nodes middle) (hl : Extends middle larger) : Extends nodes larger := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hl
  exact ⟨a ++ b, by simp [List.append_assoc]⟩

omit [DecidableEq ι] in
theorem refValid_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    {r : Ref} (hr : RefValid nodes r) : RefValid larger r := by
  obtain ⟨tail, rfl⟩ := he
  cases r <;> simp_all [RefValid]
  omega

omit [DecidableEq ι] in
theorem refSupport_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    {r : Ref} (hr : RefValid nodes r) : refSupport larger r = refSupport nodes r := by
  obtain ⟨tail, rfl⟩ := he
  cases r with
  | none => rfl
  | some i =>
    simp only [refSupport, List.map_append]
    rw [List.getElem?_append_left (by simpa [RefValid] using hr)]

/-- A constructed reference and its exact finite support, together with the
actual extension and node-count properties of the returned DAG. -/
structure Built (nodes : List (Node ι)) (result : Result ι) (support : Finset ι) (budget : ℕ) : Prop where
  valid : Valid result.1
  extension : Extends nodes result.1
  refValid : RefValid result.1 result.2
  support_eq : refSupport result.1 result.2 = support
  length_le : result.1.length ≤ nodes.length + budget

/-- The optimized constructor: omit an absent operand; otherwise intern the
addition node carrying the exact union of the actual operand supports. -/
def smartAdd (nodes : List (Node ι)) : Ref → Ref → Result ι
  | none, r => (nodes, r)
  | l, none => (nodes, l)
  | some l, some r =>
    let node : Node ι := ⟨.add l r, refSupport nodes (some l) ∪ refSupport nodes (some r)⟩
    let result := intern nodes node
    (result.1, some result.2)

private theorem intern_extends (nodes : List (Node ι)) (node : Node ι) : Extends nodes (intern nodes node).1 := by
  unfold intern
  split
  · exact extends_refl _
  · exact ⟨[node], rfl⟩

private theorem intern_length (nodes : List (Node ι)) (node : Node ι) :
    (intern nodes node).1.length ≤ nodes.length + 1 := by
  unfold intern
  split <;> simp

private theorem intern_refValid (nodes : List (Node ι)) (node : Node ι) :
    RefValid (intern nodes node).1 (some (intern nodes node).2) := by
  have hs := intern_support nodes node
  change (intern nodes node).2 < (intern nodes node).1.length
  by_contra hn
  have hn' : ((intern nodes node).1.map Node.support).length ≤ (intern nodes node).2 := by simpa using Nat.le_of_not_gt hn
  rw [List.getElem?_eq_none hn'] at hs
  contradiction

/-- Structural validity is proved from actual operand bounds and disjointness;
no external checker result or unverified support annotation is required. -/
theorem smartAdd_built (nodes : List (Node ι)) (l r : Ref) (hv : Valid nodes)
    (hl : RefValid nodes l) (hr : RefValid nodes r)
    (hd : Disjoint (refSupport nodes l) (refSupport nodes r)) :
    Built nodes (smartAdd nodes l r) (refSupport nodes l ∪ refSupport nodes r) 1 := by
  cases l with
  | none =>
    exact ⟨hv, extends_refl _, hr, by simp [smartAdd, refSupport], by simp [smartAdd]⟩
  | some l =>
    cases r with
    | none => exact ⟨hv, extends_refl _, hl, by simp [smartAdd, refSupport], by simp [smartAdd]⟩
    | some r =>
      let node : Node ι := ⟨.add l r, refSupport nodes (some l) ∪ refSupport nodes (some r)⟩
      have hn : node.Valid (nodes.map Node.support) := by
        have hl' : l < (nodes.map Node.support).length := by simpa [RefValid] using hl
        have hr' : r < (nodes.map Node.support).length := by simpa [RefValid] using hr
        simp only [Node.Valid, node, dite_eq_left hl', dite_eq_left hr', List.getElem_map]
        rw [refSupport_some nodes l hl, refSupport_some nodes r hr] at hd ⊢
        exact ⟨hd, rfl⟩
      refine ⟨intern_valid nodes node hv hn, intern_extends nodes node, intern_refValid nodes node, ?_,
        intern_length nodes node⟩
      exact congrArg (fun v : Option (Finset ι) => v.getD ∅) (intern_support nodes node)

section Values

variable [AddCommMonoid A]

def refValue (input : ι → A) (nodes : List (Node ι)) : Ref → A
  | none => 0
  | some i => (eval input nodes)[i]?.getD 0

theorem refValue_eq (input : ι → A) (nodes : List (Node ι)) (r : Ref)
    (hv : Valid nodes) (hr : RefValid nodes r) :
    refValue input nodes r = supportSum input (refSupport nodes r) := by
  cases r with
  | none => simp [refValue, refSupport, supportSum]
  | some i =>
    simp only [refValue, refSupport, eval_eq input nodes hv, List.getElem?_map,
      List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]

theorem refValue_extends (input : ι → A) {nodes larger : List (Node ι)}
    (he : Extends nodes larger) (hv : Valid nodes) (hv' : Valid larger)
    {r : Ref} (hr : RefValid nodes r) : refValue input larger r = refValue input nodes r := by
  rw [refValue_eq input larger r hv' (refValid_extends he hr), refSupport_extends he hr,
    refValue_eq input nodes r hv hr]

/-- The returned reference evaluates to the operand sum, including either or
both absent operands and the branch that reuses an earlier equal-support node. -/
theorem smartAdd_value (input : ι → A) (nodes : List (Node ι)) (l r : Ref)
    (hv : Valid nodes) (hl : RefValid nodes l) (hr : RefValid nodes r)
    (hd : Disjoint (refSupport nodes l) (refSupport nodes r)) :
    refValue input (smartAdd nodes l r).1 (smartAdd nodes l r).2 =
      refValue input nodes l + refValue input nodes r := by
  have hb := smartAdd_built nodes l r hv hl hr hd
  rw [refValue_eq input _ _ hb.valid hb.refValid, hb.support_eq,
    refValue_eq input nodes l hv hl, refValue_eq input nodes r hv hr]
  exact Finset.sum_union hd

/-- Every valid old reference retains its value after smart addition. -/
theorem smartAdd_preserves (input : ι → A) (nodes : List (Node ι)) (l r old : Ref)
    (hv : Valid nodes) (hl : RefValid nodes l) (hr : RefValid nodes r) (ho : RefValid nodes old)
    (hd : Disjoint (refSupport nodes l) (refSupport nodes r)) :
    refValue input (smartAdd nodes l r).1 old = refValue input nodes old := by
  have hb := smartAdd_built nodes l r hv hl hr hd
  exact refValue_extends input hb.extension hv hb.valid ho

end Values

/-- Explicit union semantics for an ordered finite list of references. -/
def supports (nodes : List (Node ι)) : List Ref → Finset ι
  | [] => ∅
  | r :: rs => refSupport nodes r ∪ supports nodes rs

def RefsValid (nodes : List (Node ι)) (refs : List Ref) : Prop :=
  ∀ r ∈ refs, RefValid nodes r

def DisjointRefs (nodes : List (Node ι)) (refs : List Ref) : Prop :=
  refs.Pairwise (fun l r => Disjoint (refSupport nodes l) (refSupport nodes r))

private theorem disjoint_supports (nodes : List (Node ι)) (support : Finset ι) (refs : List Ref)
    (hd : ∀ r ∈ refs, Disjoint support (refSupport nodes r)) : Disjoint support (supports nodes refs) := by
  induction refs with
  | nil => simp [supports]
  | cons r rs ih =>
    exact Finset.disjoint_union_right.mpr ⟨hd r (by simp), ih (fun s hs => hd s (by simp [hs]))⟩

/-- A right-associated finite total, with an explicit zero on the empty list.
Every recursive combination uses the same optimized smart-add constructor. -/
def total (nodes : List (Node ι)) : List Ref → Result ι
  | [] => (nodes, none)
  | r :: rs =>
    let tail := total nodes rs
    smartAdd tail.1 r tail.2

/-- The returned DAG remains valid and extends the original. Pairwise-disjoint
operands produce their exact support union using at most length minus one
new nodes, with zero new nodes on empty or singleton lists. -/
theorem total_built (nodes : List (Node ι)) (refs : List Ref) (hv : Valid nodes)
    (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    Built nodes (total nodes refs) (supports nodes refs) (refs.length - 1) := by
  induction refs with
  | nil => exact ⟨hv, extends_refl _, trivial, rfl, by simp [total]⟩
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : RefsValid nodes rs := fun s hs => hr s (by simp [hs])
    have hd0 := List.pairwise_cons.mp hd
    have ht := ih hrs hd0.2
    have hdunion := disjoint_supports nodes (refSupport nodes r) rs hd0.1
    have hadd : Disjoint (refSupport (total nodes rs).1 r) (refSupport (total nodes rs).1 (total nodes rs).2) := by
      rw [refSupport_extends ht.extension hr0, ht.support_eq]
      exact hdunion
    have ha := smartAdd_built (total nodes rs).1 r (total nodes rs).2 ht.valid
      (refValid_extends ht.extension hr0) ht.refValid hadd
    refine ⟨ha.valid, extends_trans ht.extension ha.extension, ha.refValid, ?_, ?_⟩
    · dsimp only [total]
      rw [ha.support_eq, refSupport_extends ht.extension hr0, ht.support_eq]
      rfl
    · cases rs with
      | nil => cases r <;> simp [total, smartAdd]
      | cons s ss =>
        have htlen := ht.length_le
        have halen := ha.length_le
        change (smartAdd (total nodes (s :: ss)).1 r (total nodes (s :: ss)).2).1.length ≤ _
        simp only [List.length_cons] at htlen ⊢
        omega

section TotalValues

variable [AddCommMonoid A]

private theorem supportSum_supports (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    supportSum input (supports nodes refs) = (refs.map (refValue input nodes)).sum := by
  induction refs with
  | nil => simp [supports, supportSum]
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : RefsValid nodes rs := fun s hs => hr s (by simp [hs])
    have hds := List.pairwise_cons.mp hd
    have hdu := disjoint_supports nodes (refSupport nodes r) rs hds.1
    change supportSum input (refSupport nodes r ∪ supports nodes rs) = _
    rw [show supportSum input (refSupport nodes r ∪ supports nodes rs) =
      supportSum input (refSupport nodes r) + supportSum input (supports nodes rs) from Finset.sum_union hdu]
    rw [ih hrs hds.2, ← refValue_eq input nodes r hv hr0]
    rfl

/-- The finite total evaluates to the sum of the actual original operand
values; absent operands contribute zero and shared supports are interned. -/
theorem total_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    refValue input (total nodes refs).1 (total nodes refs).2 =
      (refs.map (refValue input nodes)).sum := by
  have ht := total_built nodes refs hv hr hd
  rw [refValue_eq input _ _ ht.valid ht.refValid, ht.support_eq]
  exact supportSum_supports input nodes refs hv hr hd

theorem total_preserves (input : ι → A) (nodes : List (Node ι)) (refs : List Ref) (old : Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (ho : RefValid nodes old) : refValue input (total nodes refs).1 old = refValue input nodes old := by
  have ht := total_built nodes refs hv hr hd
  exact refValue_extends input ht.extension hv ht.valid ho

end TotalValues

end IntegerMultBounds.Networks.DisjointBuilder
