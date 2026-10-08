import IntegerMultBounds.Networks.ProjectionRank

/-! Exact rank accounting for finite wire-label updates. Every edge uses the
label actually left by preceding updates on that wire. Concrete networks must
still prove comparability and enumerate their decreasing edges. -/

namespace IntegerMultBounds.Networks.RankTrace

section Traces
variable {ι L : Type*} [DecidableEq ι]

def finish (current : ι → L) : List (ι × L) → ι → L
  | [] => current
  | (i, next) :: rest => finish (Function.update current i next) rest

def edges (current : ι → L) : List (ι × L) → List (L × L)
  | [] => []
  | (i, next) :: rest => (current i, next) :: edges (Function.update current i next) rest

def variation (dimension : L → ℕ) (current : ι → L) (updates : List (ι × L)) : ℕ :=
  ((edges current updates).map fun p =>
    (dimension p.2 - dimension p.1) + (dimension p.1 - dimension p.2)).sum

def loss (dimension : L → ℕ) (current : ι → L) (updates : List (ι × L)) : ℕ :=
  ((edges current updates).map fun p => dimension p.1 - dimension p.2).sum

def total [Fintype ι] (dimension : L → ℕ) (current : ι → L) : ℕ := ∑ i, dimension (current i)

theorem total_update [Fintype ι] (dimension : L → ℕ) (current : ι → L) (i : ι) (next : L) :
    total dimension (Function.update current i next) + dimension (current i) =
      total dimension current + dimension next := by
  have hf : (fun j => dimension (Function.update current i next j)) =
      Function.update (fun j => dimension (current j)) i (dimension next) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have ho := Finset.sum_update_of_mem (Finset.mem_univ i)
    (fun j => dimension (current j)) (dimension (current i))
  rw [Function.update_eq_self] at ho
  unfold total
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i), ho]
  omega

/-- The manuscript's telescoping identity, valid for the actual sequential
edge history even if the same wire occurs repeatedly in one gate. -/
theorem variation_balance [Fintype ι] (dimension : L → ℕ) (current : ι → L)
    (updates : List (ι × L)) :
    variation dimension current updates + total dimension current =
      total dimension (finish current updates) + 2 * loss dimension current updates := by
  induction updates generalizing current with
  | nil => simp [variation, loss, edges, finish]
  | cons p rest ih =>
    obtain ⟨i, next⟩ := p
    have ht := total_update dimension current i next
    have hr := ih (Function.update current i next)
    simp only [variation, loss, edges, List.map_cons, List.sum_cons, finish] at *
    omega

theorem edges_append (current : ι → L) (xs ys : List (ι × L)) :
    edges current (xs ++ ys) = edges current xs ++ edges (finish current xs) ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih => simp only [List.cons_append, edges, finish, ih]

theorem finish_append (current : ι → L) (xs ys : List (ι × L)) :
    finish current (xs ++ ys) = finish (finish current xs) ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih => exact ih _

theorem finish_align (current desired : ι → L) (wires : List ι) (i : ι) :
    finish current (wires.map fun j => (j, desired j)) i =
      if i ∈ wires then desired i else current i := by
  induction wires generalizing current with
  | nil => simp [finish]
  | cons j rest ih =>
    simp only [List.map_cons, finish, ih, List.mem_cons]
    by_cases hr : i ∈ rest <;> by_cases hij : i = j <;> simp [hr, hij]

end Traces

section Projections
open Module
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)

/-- An actual nondegenerate subspace, not an assigned dimension. -/
structure Label where
  space : Submodule K E
  nondegenerate : (B.restrict space).Nondegenerate

noncomputable def dimension (U : Label B) : ℕ := finrank K U.space

noncomputable def edgeRank (U V : Label B) : ℕ :=
  finrank K (LinearMap.range
    (ProjectionRank.project B hs V.space V.nondegenerate -
      ProjectionRank.project B hs U.space U.nondegenerate))

/-- Both increasing and decreasing edges have their true operator rank equal
to the absolute dimension difference. -/
theorem edgeRank_eq (U V : Label B) (h : U.space ≤ V.space ∨ V.space ≤ U.space) :
    edgeRank B hs U V = (dimension B V - dimension B U) + (dimension B U - dimension B V) := by
  rcases h with h | h
  · have hd := Submodule.finrank_mono h
    rw [edgeRank, ProjectionRank.difference_rank B hs U.space V.space
      U.nondegenerate V.nondegenerate h]
    unfold dimension
    omega
  · have hd := Submodule.finrank_mono h
    have he : ProjectionRank.project B hs V.space V.nondegenerate -
        ProjectionRank.project B hs U.space U.nondegenerate =
        -(ProjectionRank.project B hs U.space U.nondegenerate -
          ProjectionRank.project B hs V.space V.nondegenerate) := by abel
    rw [edgeRank, he, LinearMap.range_neg,
      ProjectionRank.difference_rank B hs V.space U.space V.nondegenerate U.nondegenerate h]
    unfold dimension
    omega

/-- A checked finite edge trace yields the rank sum; there is no oracle cost
attached to the updates. Endpoint and loss counts remain concrete obligations. -/
theorem rank_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (current : ι → Label B) (updates : List (ι × Label B))
    (hc : ∀ p ∈ edges current updates, p.1.space ≤ p.2.space ∨ p.2.space ≤ p.1.space) :
    ((edges current updates).map fun p => edgeRank B hs p.1 p.2).sum +
        total (dimension B) current =
      total (dimension B) (finish current updates) + 2 * loss (dimension B) current updates := by
  have he : ((edges current updates).map fun p => edgeRank B hs p.1 p.2) =
      (edges current updates).map (fun p =>
        (dimension B p.2 - dimension B p.1) + (dimension B p.1 - dimension B p.2)) := by
    apply List.map_congr_left
    intro p hp
    exact edgeRank_eq B hs p.1 p.2 (hc p hp)
  rw [he]
  exact variation_balance (dimension B) current updates

end Projections
end IntegerMultBounds.Networks.RankTrace
