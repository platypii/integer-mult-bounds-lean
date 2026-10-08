import IntegerMultBounds.Networks.DisjointBuilder

/-! Literal balanced totals from the pair-exclusion implementation: split the
input list at length divided by two, build left before right, and intern their
final addition. The construction order matters for subsequent DAG sharing. -/

namespace IntegerMultBounds.Networks.DisjointBalanced

open DisjointCircuit DisjointBuilder
variable {ι : Type*} [DecidableEq ι]

/-- Match the upstream `total` recursion, including empty/singleton elision
and left-before-right state threading at the floor-half split. -/
def total (nodes : List (Node ι)) (refs : List Ref) : DisjointBuilder.Result ι :=
  match refs with
  | [] => (nodes, none)
  | [r] => (nodes, r)
  | r :: s :: rs =>
    let values := r :: s :: rs
    let left := total nodes (values.take (values.length / 2))
    let right := total left.1 (values.drop (values.length / 2))
    smartAdd right.1 left.2 right.2
termination_by refs.length
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem supports_append (nodes : List (Node ι)) (xs ys : List Ref) :
    supports nodes (xs ++ ys) = supports nodes xs ∪ supports nodes ys := by
  induction xs with
  | nil => simp [supports]
  | cons x xs ih => simp [supports, ih, Finset.union_assoc]

private theorem disjoint_union (nodes : List (Node ι)) (s : Finset ι) (rs : List Ref)
    (hd : ∀ r ∈ rs, Disjoint s (refSupport nodes r)) : Disjoint s (supports nodes rs) := by
  induction rs with
  | nil => simp [supports]
  | cons r rs ih =>
    exact Finset.disjoint_union_right.mpr ⟨hd r (by simp), ih (fun x hx => hd x (by simp [hx]))⟩

private theorem disjoint_unions (nodes : List (Node ι)) (xs ys : List Ref)
    (hd : ∀ x ∈ xs, ∀ y ∈ ys, Disjoint (refSupport nodes x) (refSupport nodes y)) :
    Disjoint (supports nodes xs) (supports nodes ys) := by
  induction xs with
  | nil => simp [supports]
  | cons x xs ih =>
    exact Finset.disjoint_union_left.mpr
      ⟨disjoint_union nodes _ ys (hd x (by simp)), ih (fun x hx => hd x (by simp [hx]))⟩

omit [DecidableEq ι] in
private theorem refsValid_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    {refs : List Ref} (hr : RefsValid nodes refs) : RefsValid larger refs :=
  fun r h => refValid_extends he (hr r h)

private theorem supports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : supports larger refs = supports nodes refs := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    simp only [supports]
    rw [refSupport_extends he (hr r (by simp)), ih (fun s hs => hr s (by simp [hs]))]

omit [DecidableEq ι] in
private theorem disjointRefs_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    DisjointRefs larger refs := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rw [refSupport_extends he (hr _ (List.getElem_mem hi)),
    refSupport_extends he (hr _ (List.getElem_mem hj))]
  exact List.pairwise_iff_getElem.mp hd i j hi hj hij

/-- Balanced recursion constructs the exact disjoint union, preserving all
old references, with at most length-minus-one new DAG nodes. -/
theorem total_built (nodes : List (Node ι)) (refs : List Ref) (hv : Valid nodes)
    (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    Built nodes (total nodes refs) (supports nodes refs) (refs.length - 1) := by
  induction refs using (measure (fun rs : List Ref => rs.length)).wf.induction generalizing nodes with
  | h refs ih =>
    cases refs with
    | nil =>
      simp only [total]
      exact ⟨hv, extends_refl _, trivial, rfl, by simp⟩
    | cons r tail =>
      cases tail with
      | nil =>
        simp only [total]
        exact ⟨hv, extends_refl _, hr r (by simp), by simp [supports], by simp⟩
      | cons s rs =>
        let values := r :: s :: rs
        let left := values.take (values.length / 2)
        let right := values.drop (values.length / 2)
        have hsplit : left ++ right = values := List.take_append_drop _ _
        have hlen : 2 ≤ values.length := by simp [values]
        have hl : left.length < values.length := by simp only [left, List.length_take]; omega
        have hr' : right.length < values.length := by simp only [right, List.length_drop]; omega
        have hlpos : 0 < left.length := by simp only [left, List.length_take]; omega
        have hrpos : 0 < right.length := by simp only [right, List.length_drop]; omega
        have hlv : RefsValid nodes left := fun x hx => hr x ((List.take_sublist _ values).subset hx)
        have hrv : RefsValid nodes right := fun x hx => hr x ((List.drop_sublist _ values).subset hx)
        have hp := List.pairwise_append.mp (show DisjointRefs nodes (left ++ right) from by
          rw [hsplit]; exact hd)
        have bl := ih left hl nodes hv hlv hp.1
        have br := ih right hr' (total nodes left).1 bl.valid
          (refsValid_extends bl.extension hrv) (disjointRefs_extends bl.extension right hrv hp.2.1)
        have hext := extends_trans bl.extension br.extension
        have hleft : refSupport (total (total nodes left).1 right).1 (total nodes left).2 = supports nodes left := by
          rw [refSupport_extends br.extension bl.refValid, bl.support_eq]
        have hright : refSupport (total (total nodes left).1 right).1 (total (total nodes left).1 right).2 =
            supports nodes right := by
          rw [br.support_eq, supports_extends bl.extension right hrv]
        have ba := smartAdd_built _ _ _ br.valid (refValid_extends br.extension bl.refValid) br.refValid (by
          rw [hleft, hright]
          exact disjoint_unions nodes left right hp.2.2)
        rw [total]
        change Built nodes (smartAdd (total (total nodes left).1 right).1
          (total nodes left).2 (total (total nodes left).1 right).2) (supports nodes values) (values.length - 1)
        refine ⟨ba.valid, extends_trans hext ba.extension, ba.refValid, ?_, ?_⟩
        · rw [ba.support_eq, hleft, hright, ← supports_append, hsplit]
        · have h1 := bl.length_le
          have h2 := br.length_le
          have h3 := ba.length_le
          have hlenEq : left.length + right.length = values.length := by
            rw [← List.length_append, hsplit]
          omega

section Values
variable {A : Type*} [AddCommMonoid A]

/-- The literal balanced constructor evaluates to the sum of all original
operands, irrespective of zero elision or reuse by support interning. -/
theorem total_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    refValue input (total nodes refs).1 (total nodes refs).2 =
      (refs.map (refValue input nodes)).sum := by
  have hb := total_built nodes refs hv hr hd
  have old := DisjointBuilder.total_built nodes refs hv hr hd
  have ho := DisjointBuilder.total_value input nodes refs hv hr hd
  rw [refValue_eq input _ _ old.valid old.refValid, old.support_eq] at ho
  rw [refValue_eq input _ _ hb.valid hb.refValid, hb.support_eq]
  exact ho

/-- The actual balanced construction preserves all existing source values. -/
theorem total_preserves (input : ι → A) (nodes : List (Node ι)) (refs : List Ref) (old : Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (ho : RefValid nodes old) :
    refValue input (total nodes refs).1 old = refValue input nodes old := by
  have hb := total_built nodes refs hv hr hd
  exact refValue_extends input hb.extension hv hb.valid ho
end Values
end IntegerMultBounds.Networks.DisjointBalanced
