import IntegerMultBounds.Networks.DuplicateBudget

/-! Duplicate witnesses across actual common-point copies automatically form
a matching. A nontrivial triple support has at most two common points; local
support uniqueness therefore rules out repeated right endpoints, and the
increasing common-point orientation rules out chains of overlapping matches.
No disjointness assumption is imposed on the witness certificate itself. -/

namespace IntegerMultBounds.Networks.SharedPointMatching

open NeighborCounts SharedPointKey

/-- A physical local node name retains its common-point copy and local index. -/
abbrev CopyNode (h : ℕ) := Fin h × ℕ

/-- The actual nontrivial supports of a common-point circuit family. Every
active node is an addition support, and each local copy interns equal supports. -/
structure Family (h : ℕ) where
  domain : Finset (CopyNode h)
  support : CopyNode h → Finset (Triple h)
  nontrivial : ∀ n ∈ domain, 2 ≤ (support n).card
  common : ∀ n ∈ domain, ∀ T ∈ support n, n.1 ∈ T.val
  unique : ∀ a ∈ domain, ∀ b ∈ domain,
    a.1 = b.1 → support a = support b → a = b

variable {h : ℕ}

/-- A certificate entry gives two actual equal supports in distinct local
copies, oriented by their strictly increasing common-point identifiers. -/
structure IsWitness (family : Family h) (pair : CopyNode h × CopyNode h) : Prop where
  left_mem : pair.1 ∈ family.domain
  right_mem : pair.2 ∈ family.domain
  ordered : pair.1.1 < pair.2.1
  equal : family.support pair.1 = family.support pair.2

theorem common_mem (family : Family h) (n : CopyNode h) (hn : n ∈ family.domain) :
    n.1 ∈ core (family.support n) := (mem_core _ _).mpr (family.common n hn)

/-- Every witnessed duplicate's exact common core consists of its two copy
identifiers; there is no third common-point copy carrying this support. -/
theorem witness_core (family : Family h) (pair : CopyNode h × CopyNode h)
    (hw : IsWitness family pair) :
    core (family.support pair.1) = {pair.1.1, pair.2.1} := by
  have hl := common_mem family pair.1 hw.left_mem
  have hr := common_mem family pair.2 hw.right_mem
  rw [← hw.equal] at hr
  have hsub : ({pair.1.1, pair.2.1} : Finset (Fin h)) ⊆ core (family.support pair.1) :=
    Finset.insert_subset hl (Finset.singleton_subset_iff.mpr hr)
  have hcard := DuplicateBudget.core_card_le_two _ (family.nontrivial pair.1 hw.left_mem)
  have hne : pair.1.1 ≠ pair.2.1 := ne_of_lt hw.ordered
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa [hne] using hcard)).symm

/-- Distinct genuine witness pairs cannot discard the same right node. The
core determines its partner copy, and local uniqueness determines its index. -/
theorem right_injective (family : Family h) (witnesses : Finset (CopyNode h × CopyNode h))
    (hw : ∀ pair ∈ witnesses, IsWitness family pair) : Set.InjOn (Prod.snd : CopyNode h × CopyNode h → CopyNode h) witnesses := by
  intro m hm n hn he
  have hm' := hw m hm
  have hn' := hw n hn
  have heq : family.support m.1 = family.support n.1 :=
    hm'.equal.trans ((congrArg family.support he).trans hn'.equal.symm)
  have hcommon := common_mem family n.1 hn'.left_mem
  rw [← heq, witness_core family m hm'] at hcommon
  have hright : m.2.1 = n.2.1 := congrArg Prod.fst he
  have howner : m.1.1 = n.1.1 := by
    rcases Finset.mem_insert.mp hcommon with hc | hc
    · exact hc.symm
    · have hc' := Finset.mem_singleton.mp hc
      have ho := hn'.ordered
      rw [hc', ← hright] at ho
      exact False.elim (lt_irrefl _ ho)
  exact Prod.ext (family.unique m.1 hm'.left_mem n.1 hn'.left_mem howner heq) he

/-- No surviving left endpoint is any discarded right endpoint. An overlap
would place three strictly ordered copy identifiers in one two-point core. -/
theorem endpoints_separate (family : Family h) (witnesses : Finset (CopyNode h × CopyNode h))
    (hw : ∀ pair ∈ witnesses, IsWitness family pair) :
    ∀ m ∈ witnesses, ∀ n ∈ witnesses, m.1 ≠ n.2 := by
  intro m hm n hn he
  have hm' := hw m hm
  have hn' := hw n hn
  have hcommon := common_mem family n.1 hn'.left_mem
  have heq : family.support n.1 = family.support m.1 :=
    hn'.equal.trans (congrArg family.support he.symm)
  rw [heq, witness_core family m hm'] at hcommon
  have howner : m.1.1 = n.2.1 := congrArg Prod.fst he
  have hlo : n.1.1 < m.1.1 := by simpa only [howner] using hn'.ordered
  rcases Finset.mem_insert.mp hcommon with hc | hc
  · exact (ne_of_lt hlo) hc
  · have hc' := Finset.mem_singleton.mp hc
    exact (not_lt_of_ge (le_of_lt hm'.ordered)) (hc' ▸ hlo)

/-- Genuine equal-support pairs alone supply the required matching properties;
the finite certificate need not separately assert endpoint disjointness. -/
theorem image_card_add_witnesses_le (family : Family h)
    (witnesses : Finset (CopyNode h × CopyNode h))
    (hw : ∀ pair ∈ witnesses, IsWitness family pair) :
    (family.domain.image family.support).card + witnesses.card ≤ family.domain.card :=
  DuplicateBudget.image_card_add_witnesses_le family.domain witnesses Prod.fst Prod.snd family.support
    (fun m hm => (hw m hm).left_mem) (fun m hm => (hw m hm).right_mem)
    (right_injective family witnesses hw) (endpoints_separate family witnesses hw)
    (fun m hm => (hw m hm).equal)

/-- For the fifty-copy family, the two concrete counts and genuine duplicate
pairs suffice for the optimized allocation bound; matching is proved above. -/
theorem h50_bound (family : Family 50) (witnesses : Finset (CopyNode 50 × CopyNode 50))
    (hw : ∀ pair ∈ witnesses, IsWitness family pair)
    (hd : family.domain.card ≤ 50 * 9813) (hm : 40256 ≤ witnesses.card) :
    (family.domain.image family.support).card ≤ 450394 :=
  DuplicateBudget.h50_bound family.domain witnesses Prod.fst Prod.snd family.support
    (fun m hm => (hw m hm).left_mem) (fun m hm => (hw m hm).right_mem)
    (right_injective family witnesses hw) (endpoints_separate family witnesses hw)
    (fun m hm => (hw m hm).equal) hd hm

end IntegerMultBounds.Networks.SharedPointMatching
