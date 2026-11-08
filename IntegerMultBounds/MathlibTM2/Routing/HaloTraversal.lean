module

public import IntegerMultBounds.MathlibTM2.Routing.HaloStageParameters

/-! Build stage data in one distinct axis traversal. The program remains the
fixed runtime loop: this list contains metadata, not unrolled executable code. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloTraversal
open RetainedHaloTensor HaloAxisSchedule HaloStageParameters
variable {ι : Type} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem fresh (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup) :
    i ∉ left.toFinset := by
  intro hi
  exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 (List.mem_toFinset.mp hi) (by simp)

def build (axis : ι → Axis) (w : ℕ) (hw : 0 < w) (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅) (left : List ι) :
    (todo : List ι) → (left++todo).Nodup → (∀ j, j ∈ left++todo) → List (Stage ι)
  | [], _, _ => []
  | i::right, hn, hall =>
    stage axis left.toFinset left i right hn hall (fresh left i right hn) w hw (hgap i) (hv _) ::
      build axis w hw hgap hv (left++[i]) right
        (by simpa only [List.append_assoc,List.singleton_append] using hn)
        (by simpa only [List.append_assoc,List.singleton_append] using hall)

theorem build_indices (axis : ι → Axis) (w : ℕ) (hw : 0 < w)
    (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅)
    (left todo : List ι) (hn : (left++todo).Nodup) (hall : ∀ j, j ∈ left++todo) :
    (build axis w hw hgap hv left todo hn hall).map Stage.i = todo := by
  induction todo generalizing left with
  | nil => rfl
  | cons i right ih => simp only [build,List.map_cons,stage]; rw [ih]

theorem build_order (axis : ι → Axis) (w : ℕ) (hw : 0 < w)
    (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅)
    (left todo : List ι) (hn : (left++todo).Nodup) (hall : ∀ j, j ∈ left++todo) :
    ∀ s ∈ build axis w hw hgap hv left todo hn hall, s.left++s.i::s.right = left++todo := by
  induction todo generalizing left with
  | nil => simp [build]
  | cons i right ih =>
    intro s hs
    simp only [build,List.mem_cons] at hs
    rcases hs with rfl | hs
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using ih (left++[i]) _ _ s hs

theorem build_ready (axis : ι → Axis) (w : ℕ) (hw : 0 < w)
    (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅)
    (left todo : List ι) (hn : (left++todo).Nodup) (hall : ∀ j, j ∈ left++todo) :
    ∀ done s rest, build axis w hw hgap hv left todo hn hall = done++s::rest →
      Ready axis (after left.toFinset done) s := by
  induction todo generalizing left with
  | nil => intro done s rest he; simp [build] at he
  | cons i right ih =>
    intro done s rest he
    cases done with
    | nil =>
      simp only [build,List.nil_append,List.cons.injEq] at he
      obtain ⟨rfl,_⟩ := he
      exact stage_ready axis left.toFinset left i right hn hall (fresh left i right hn) w hw (hgap i) (hv _)
    | cons t done =>
      simp only [build,List.cons_append,List.cons.injEq] at he
      obtain ⟨rfl,he⟩ := he
      have hh := ih (left++[i]) _ _ done s rest he
      simpa only [after,stage,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
        Finset.union_insert,Finset.union_empty] using hh

theorem build_params (axis : ι → Axis) (w : ℕ) (hw : 0 < w)
    (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅)
    (left todo : List ι) (hn : (left++todo).Nodup) (hall : ∀ j, j ∈ left++todo) :
    ∀ s ∈ build axis w hw hgap hv left todo hn hall,
      s.params.w = w ∧ s.params.V = HaloMetadataFit.metadataWidth (volume axis ∅) w (left++todo).length := by
  induction todo generalizing left with
  | nil => simp [build]
  | cons i right ih =>
    intro s hs
    simp only [build,List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨rfl,rfl⟩
    · simpa only [List.append_assoc,List.singleton_append] using ih (left++[i]) _ _ s hs

theorem build_sizing (axis : ι → Axis) (w : ℕ) (hw : 0 < w)
    (hgap : ∀ i, 2*(axis i).H ≤ (axis i).L)
    (hv : ∀ retained, volume axis retained ≤ 2*volume axis ∅)
    (hcoarse : ∀ i, (axis i).L ≤ (axis i).N)
    (left todo : List ι) (hn : (left++todo).Nodup) (hall : ∀ j, j ∈ left++todo) :
    ∀ s ∈ build axis w hw hgap hv left todo hn hall,
      s.params.L ≤ s.params.N ∧ s.params.k = Nat.clog 2 s.params.L ∧
        s.params.r = Nat.clog 2 (s.params.L+2*s.params.H) := by
  induction todo generalizing left with
  | nil => simp [build]
  | cons i right ih =>
    intro s hs
    simp only [build,List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨hcoarse i,rfl,rfl⟩
    · exact ih (left++[i]) _ _ s hs

end IntegerMultBounds.MathlibTM2.Routing.HaloTraversal
