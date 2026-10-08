import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Literal consecutive-pair grouping for the paired exclusion recursion.
The last group is a singleton for odd input lengths. The list and finite-set
interfaces retain the input order and prove the partition properties used
by the coarse graph construction. -/

namespace IntegerMultBounds.Networks.PairGrouping

variable {V : Type*}

/-- The upstream slices `points[i:i+2]`, for `i = 0, 2, 4, ...`. -/
def groups : List V → List (List V)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest => [a, b] :: groups rest

@[simp] theorem flatten_groups (points : List V) : (groups points).flatten = points := by
  fun_induction groups points <;> simp_all

/-- The number of groups is the integer ceiling of half the input length. -/
theorem length_groups (points : List V) : (groups points).length = (points.length + 1) / 2 := by
  fun_induction groups points <;> simp_all
  omega

theorem group_nonempty (points : List V) (g : List V) (hg : g ∈ groups points) : g ≠ [] := by
  fun_induction groups points <;> simp_all
  aesop

theorem group_length_le (points : List V) (g : List V) (hg : g ∈ groups points) : g.length ≤ 2 := by
  fun_induction groups points <;> simp_all
  aesop

/-- Group number `i` is literally the upstream length-two slice starting at `2*i`. -/
theorem getElem_groups (points : List V) (i : ℕ) (hi : i < (groups points).length) :
    (groups points)[i] = (points.drop (2 * i)).take 2 := by
  fun_induction groups points generalizing i with
  | case1 => simp only [List.length_nil] at hi; omega
  | case2 a =>
    have he : i = 0 := by simpa using hi
    subst i
    rfl
  | case3 a b rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < (groups rest).length := by simpa using hi
      simpa [groups, Nat.mul_add, List.drop_succ_cons] using ih i hi'

/-- The coarse recursive call strictly decreases beyond the small-block branch. -/
theorem length_groups_lt (points : List V) (h : 4 < points.length) :
    (groups points).length < points.length := by
  rw [length_groups]
  omega

theorem mem_group (points : List V) (v : V) :
    (∃ g ∈ groups points, v ∈ g) ↔ v ∈ points := by
  rw [← List.mem_flatten, flatten_groups]

theorem group_subset (points : List V) (g : List V) (hg : g ∈ groups points) : g ⊆ points :=
  fun _ hv => (mem_group points _).mp ⟨g, hg, hv⟩

theorem group_nodup (points : List V) (hn : points.Nodup) :
    ∀ g ∈ groups points, g.Nodup :=
  (List.nodup_flatten.mp (by simpa using hn : (groups points).flatten.Nodup)).1

theorem groups_disjoint (points : List V) (hn : points.Nodup) :
    (groups points).Pairwise List.Disjoint :=
  (List.nodup_flatten.mp (by simpa using hn : (groups points).flatten.Nodup)).2

section Finsets
variable [DecidableEq V]

/-- Ordered coarse vertices, represented by their actual fine-vertex sets. -/
def finsets (points : List V) : List (Finset V) := (groups points).map List.toFinset

@[simp] theorem length_finsets (points : List V) :
    (finsets points).length = (points.length + 1) / 2 := by
  simp [finsets, length_groups]

theorem finsets_length_lt (points : List V) (h : 4 < points.length) :
    (finsets points).length < points.length := by
  rw [length_finsets]
  omega

theorem finset_nonempty (points : List V) (g : Finset V) (hg : g ∈ finsets points) : g.Nonempty := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil l (group_nonempty points l hl)
  exact ⟨v, List.mem_toFinset.mpr hv⟩

theorem finset_card_le (points : List V) (g : Finset V) (hg : g ∈ finsets points) : g.card ≤ 2 := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  exact (List.toFinset_card_le _).trans (group_length_le points l hl)

theorem mem_finset (points : List V) (v : V) :
    (∃ g ∈ finsets points, v ∈ g) ↔ v ∈ points := by
  simp only [finsets, List.mem_map, exists_exists_and_eq_and, List.mem_toFinset]
  exact mem_group points v

theorem finsets_disjoint (points : List V) (hn : points.Nodup) :
    (finsets points).Pairwise Disjoint := by
  apply List.pairwise_map.mpr
  exact (groups_disjoint points hn).imp (fun h => List.disjoint_toFinset_iff_disjoint.mpr h)

/-- Nonempty disjoint groups are distinct, so they can safely index coarse vertices. -/
theorem finsets_nodup (points : List V) (hn : points.Nodup) : (finsets points).Nodup := by
  apply List.Pairwise.imp_of_mem _ (finsets_disjoint points hn)
  intro g t hg _ hd he
  subst t
  obtain ⟨v, hv⟩ := finset_nonempty points g hg
  exact Finset.disjoint_left.mp hd hv hv

end Finsets
end IntegerMultBounds.Networks.PairGrouping
