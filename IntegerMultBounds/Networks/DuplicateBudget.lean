import IntegerMultBounds.Networks.SharedPointKey
import Mathlib.Data.Finset.Card

/-! Cardinal savings from certified pairs of equal circuit supports. Deleting
one endpoint of each disjoint match preserves all represented supports, so a
list of genuine duplicate witnesses gives an upper bound without requiring
an exhaustive global hash-table computation. -/

namespace IntegerMultBounds.Networks.DuplicateBudget

variable {α β μ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq μ]

omit [DecidableEq μ] in
/-- Remove the right endpoint of every certified duplicate match. The left
endpoint survives, and represents exactly the same value. -/
theorem image_erase_witnesses (domain : Finset α) (witnesses : Finset μ)
    (left right : μ → α) (value : α → β)
    (hl : ∀ m ∈ witnesses, left m ∈ domain)
    (hsep : ∀ m ∈ witnesses, ∀ n ∈ witnesses, left m ≠ right n)
    (heq : ∀ m ∈ witnesses, value (left m) = value (right m)) :
    domain.image value = (domain \ witnesses.image right).image value := by
  apply Finset.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    by_cases hd : a ∈ witnesses.image right
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
      refine Finset.mem_image.mpr ⟨left m, Finset.mem_sdiff.mpr ⟨hl m hm, ?_⟩, heq m hm⟩
      rintro hn
      obtain ⟨n, hn, hen⟩ := Finset.mem_image.mp hn
      exact hsep m hm n hn hen.symm
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨ha, hd⟩, rfl⟩
  · exact Finset.image_subset_image Finset.sdiff_subset

omit [DecidableEq μ] in
/-- Each distinct discarded endpoint saves one represented object. The
certificate need not enumerate all duplicates: additional sharing only helps. -/
theorem image_card_add_witnesses_le (domain : Finset α) (witnesses : Finset μ)
    (left right : μ → α) (value : α → β)
    (hl : ∀ m ∈ witnesses, left m ∈ domain)
    (hr : ∀ m ∈ witnesses, right m ∈ domain)
    (hinj : Set.InjOn right witnesses)
    (hsep : ∀ m ∈ witnesses, ∀ n ∈ witnesses, left m ≠ right n)
    (heq : ∀ m ∈ witnesses, value (left m) = value (right m)) :
    (domain.image value).card + witnesses.card ≤ domain.card := by
  rw [image_erase_witnesses domain witnesses left right value hl hsep heq]
  have hsub : witnesses.image right ⊆ domain := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    exact hr m hm
  have hcard : (witnesses.image right).card = witnesses.card := Finset.card_image_of_injOn hinj
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  have hle := Finset.card_image_le (s := domain \ witnesses.image right) (f := value)
  omega

open SharedPointKey NeighborCounts

/-- A nontrivial addition of triples has at most two common points. This
excludes a duplicate sum appearing in three distinct common-point copies. -/
theorem core_card_le_two {h : ℕ} (support : Finset (Triple h)) (hs : 2 ≤ support.card) :
    (core support).card ≤ 2 := by
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < support.card)
  have hcS := core_subset support S hS
  have hcT := core_subset support T hT
  have hle : (core support).card ≤ 3 := by simpa [S.property] using Finset.card_le_card hcS
  by_contra hn
  have hcard : (core support).card = 3 := by omega
  have hS' : core support = S.val := Finset.eq_of_subset_of_card_le hcS (by rw [hcard, S.property])
  have hT' : core support = T.val := Finset.eq_of_subset_of_card_le hcT (by rw [hcard, T.property])
  exact hne (Subtype.ext (hS'.symm.trans hT'))

omit [DecidableEq μ] in
/-- Fifty local copies with at most 9,813 additions, together with 40,256
certified disjoint duplicate witnesses, imply the optimized allocation bound.
The finite circuit certificate must supply these concrete counts. -/
theorem h50_bound (domain : Finset α) (witnesses : Finset μ)
    (left right : μ → α) (value : α → β)
    (hl : ∀ m ∈ witnesses, left m ∈ domain)
    (hr : ∀ m ∈ witnesses, right m ∈ domain)
    (hinj : Set.InjOn right witnesses)
    (hsep : ∀ m ∈ witnesses, ∀ n ∈ witnesses, left m ≠ right n)
    (heq : ∀ m ∈ witnesses, value (left m) = value (right m))
    (hd : domain.card ≤ 50 * 9813) (hm : 40256 ≤ witnesses.card) :
    (domain.image value).card ≤ 450394 := by
  have hh := image_card_add_witnesses_le domain witnesses left right value hl hr hinj hsep heq
  omega

end IntegerMultBounds.Networks.DuplicateBudget
