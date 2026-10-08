import IntegerMultBounds.Networks.NeighborCounts
import Mathlib.Combinatorics.Hall.Finite

/-! A neighbor permutation of finite triple banks. This is a finite Hall
existence construction from the exact regular neighbor census. It supplies
the bijection needed for stage reuse, but does not formalize or identify the
explicit paired-point generator in `scripts/reuse_network.py`. -/

namespace IntegerMultBounds.Networks.TripleNeighborPermutation

open NeighborCounts

/-- A finite relation with equal positive row and column degrees satisfies
Hall's condition, by counting its incidences on an arbitrary source subset. -/
theorem regular_hall {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (degree : ℕ) (hd : 0 < degree)
    (hrow : ∀ x, (Finset.univ.filter (R x)).card = degree)
    (hcol : ∀ y, (Finset.univ.filter (fun x => R x y)).card = degree)
    (s : Finset α) : s.card ≤ (s.biUnion (fun x => Finset.univ.filter (R x))).card := by
  let targets := s.biUnion (fun x => Finset.univ.filter (R x))
  have hfilter (x : α) (hx : x ∈ s) : targets.filter (R x) = Finset.univ.filter (R x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hxy
      exact ⟨Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩, hxy⟩
  have hcount : s.card * degree ≤ targets.card * degree := by
    calc
      s.card * degree = ∑ x ∈ s, (targets.filter (R x)).card := by
        symm
        calc
          _ = ∑ _x ∈ s, degree := Finset.sum_congr rfl (fun x hx => by rw [hfilter x hx, hrow])
          _ = _ := by simp
      _ = ∑ x ∈ s, ∑ y ∈ targets, if R x y then 1 else 0 := by simp
      _ = ∑ y ∈ targets, ∑ x ∈ s, if R x y then 1 else 0 := Finset.sum_comm
      _ = ∑ y ∈ targets, (s.filter (fun x => R x y)).card := by simp
      _ ≤ ∑ y ∈ targets, degree := by
        apply Finset.sum_le_sum
        intro y _
        rw [← hcol y]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
      _ = targets.card * degree := by simp
  exact Nat.le_of_mul_le_mul_right hcount hd

/-- Finite regular bipartite relations admit a bijective choice of neighbors. -/
theorem exists_equiv_of_regular {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (degree : ℕ) (hd : 0 < degree)
    (hrow : ∀ x, (Finset.univ.filter (R x)).card = degree)
    (hcol : ∀ y, (Finset.univ.filter (fun x => R x y)).card = degree) :
    ∃ e : α ≃ α, ∀ x, R x (e x) := by
  obtain ⟨f, hf, hn⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x => Finset.univ.filter (R x))).mp (regular_hall R degree hd hrow hcol)
  let e : α ≃ α := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  exact ⟨e, fun x => (Finset.mem_filter.mp (hn x)).2⟩

/-- The already-proved neighbor census, expressed as the row degree used by
Hall's finite matching theorem. -/
theorem neighbor_degree (h : ℕ) (T : Triple h) :
    (Finset.univ.filter (BitNeighbor T)).card = 3 * (h - 3).choose 2 := by
  simpa only [Fintype.card_subtype] using bit_neighbor_card T

/-- At fifty points each left and right vertex has exactly 3243 neighbors. -/
theorem neighbor_degree50 (T : Triple 50) :
    (Finset.univ.filter (BitNeighbor T)).card = 3243 := neighbor_degree 50 T

/-- The stage-reuse requirement is satisfiable on the actual fifty-point
triple bank, without a supplied matching or cardinality assumption. -/
theorem exists_permutation50 : ∃ e : Triple 50 ≃ Triple 50, ∀ T, BitNeighbor T (e T) := by
  apply exists_equiv_of_regular BitNeighbor 3243 (by decide) neighbor_degree50
  intro T
  have he : (Finset.univ.filter (fun S : Triple 50 => BitNeighbor S T)) =
      Finset.univ.filter (BitNeighbor T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, BitNeighbor, Finset.inter_comm]
  rw [he, neighbor_degree50]

/-- A fixed Hall-selected permutation. It is not asserted to equal the
upstream paired-point implementation. -/
noncomputable def permutation50 : Triple 50 ≃ Triple 50 := Classical.choose exists_permutation50

theorem permutation50_neighbor (T : Triple 50) : BitNeighbor T (permutation50 T) :=
  Classical.choose_spec exists_permutation50 T

theorem permutation50_intersection (T : Triple 50) : (T.val ∩ (permutation50 T).val).card = 1 :=
  permutation50_neighbor T

/-- The inverse also pairs each triple with an intersection-one neighbor. -/
theorem inverse50_neighbor (T : Triple 50) : BitNeighbor T (permutation50.symm T) := by
  have hh := permutation50_neighbor (permutation50.symm T)
  simpa only [Equiv.apply_symm_apply, BitNeighbor, Finset.inter_comm] using hh

end IntegerMultBounds.Networks.TripleNeighborPermutation
