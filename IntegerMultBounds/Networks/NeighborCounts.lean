import IntegerMultBounds.Networks.Scalar
import Mathlib.Data.Fintype.Powerset

/-! Cardinalities of the actual finite triple banks and their neighbor sets.
Counting uses a bijection that splits each triple into its intersection with a
fixed set and its complementary part; no numerical wire counts are assumed. -/

namespace IntegerMultBounds.Networks

namespace NeighborCounts

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A fixed-size subset with a prescribed intersection cardinality. -/
abbrev Fiber (S : Finset α) (t k : ℕ) :=
  {T : Finset α // T.card = t ∧ (S ∩ T).card = k}

private theorem split_union_left (S A B : Finset α) (hA : A ⊆ S)
    (hB : B ⊆ Finset.univ \ S) : S ∩ (A ∪ B) = A := by
  ext i
  have ha : i ∈ A → i ∈ S := fun h => hA h
  have hb : i ∈ B → i ∉ S := fun h => (Finset.mem_sdiff.mp (hB h)).2
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

private theorem split_union_right (S A B : Finset α) (hA : A ⊆ S)
    (hB : B ⊆ Finset.univ \ S) : (A ∪ B) \ S = B := by
  ext i
  have ha : i ∈ A → i ∈ S := fun h => hA h
  have hb : i ∈ B → i ∉ S := fun h => (Finset.mem_sdiff.mp (hB h)).2
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- Choose the intersection and outside part independently, retaining both
actual finite subsets rather than just their cardinalities. -/
def splitEquiv (S : Finset α) (t k : ℕ) (hk : k ≤ t) :
    Fiber S t k ≃ {A // A ∈ S.powersetCard k} ×
      {B // B ∈ (Finset.univ \ S).powersetCard (t - k)} where
  toFun T :=
    (⟨S ∩ T.val, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, T.property.2⟩⟩,
     ⟨T.val \ S, Finset.mem_powersetCard.mpr ⟨by
       intro i hi
       exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩,
       by rw [Finset.card_sdiff, T.property.1, T.property.2]⟩⟩)
  invFun p := ⟨p.1.val ∪ p.2.val, by
    obtain ⟨hA, hcA⟩ := Finset.mem_powersetCard.mp p.1.property
    obtain ⟨hB, hcB⟩ := Finset.mem_powersetCard.mp p.2.property
    have hd : Disjoint p.1.val p.2.val := by
      apply Finset.disjoint_left.mpr
      intro i hiA hiB
      exact (Finset.mem_sdiff.mp (hB hiB)).2 (hA hiA)
    constructor
    · rw [Finset.card_union_of_disjoint hd, hcA, hcB]
      omega
    · rw [split_union_left S _ _ hA hB, hcA]⟩
  left_inv T := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv p := by
    obtain ⟨hA, _⟩ := Finset.mem_powersetCard.mp p.1.property
    obtain ⟨hB, _⟩ := Finset.mem_powersetCard.mp p.2.property
    apply Prod.ext <;> apply Subtype.ext
    · exact split_union_left S _ _ hA hB
    · exact split_union_right S _ _ hA hB

/-- The generic intersection census, valid for every finite ground set. -/
theorem fiber_card (S : Finset α) (t k : ℕ) (hk : k ≤ t) :
    Fintype.card (Fiber S t k) = S.card.choose k * (Fintype.card α - S.card).choose (t - k) := by
  rw [Fintype.card_congr (splitEquiv S t k hk), Fintype.card_prod]
  simp only [Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

abbrev Triple (h : ℕ) := {S : Finset (Fin h) // S.card = 3}

@[simp] theorem triple_card (h : ℕ) : Fintype.card (Triple h) = h.choose 3 := by
  simp [Triple]

theorem triple_intersection_card {h : ℕ} (S : Triple h) (k : ℕ) (hk : k ≤ 3) :
    Fintype.card {T : Triple h // (S.val ∩ T.val).card = k} =
      (3 : ℕ).choose k * (h - 3).choose (3 - k) := by
  let e : {T : Triple h // (S.val ∩ T.val).card = k} ≃ Fiber S.val 3 k :=
    { toFun := fun T => ⟨T.val.val, T.val.property, T.property⟩
      invFun := fun T => ⟨⟨T.val, T.property.1⟩, T.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, fiber_card _ _ _ hk, S.property, Fintype.card_fin]

/-- Neighbor predicates match the bit and complex scalar-motif definitions. -/
def BitNeighbor {h : ℕ} (S T : Triple h) : Prop := (S.val ∩ T.val).card = 1

def ComplexNeighbor {h : ℕ} (S T : Triple h) : Prop :=
  S.val ≠ T.val ∧ Even (S.val ∩ T.val).card

instance {h : ℕ} (S T : Triple h) : Decidable (BitNeighbor S T) :=
  inferInstanceAs (Decidable ((S.val ∩ T.val).card = 1))

instance {h : ℕ} (S T : Triple h) : Decidable (ComplexNeighbor S T) :=
  inferInstanceAs (Decidable (S.val ≠ T.val ∧ Even (S.val ∩ T.val).card))

theorem bit_neighbor_card {h : ℕ} (S : Triple h) :
    Fintype.card {T : Triple h // BitNeighbor S T} = 3 * (h - 3).choose 2 := by
  calc
    Fintype.card {T : Triple h // BitNeighbor S T} =
        Fintype.card {T : Triple h // (S.val ∩ T.val).card = 1} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
    _ = 3 * (h - 3).choose 2 := by simpa using triple_intersection_card S 1 (by omega)

/-- Distinct triples with even intersection are exactly the disjoint triples
and those sharing two coordinates. -/
theorem complex_neighbor_iff {h : ℕ} (S T : Triple h) :
    ComplexNeighbor S T ↔ (S.val ∩ T.val).card = 0 ∨ (S.val ∩ T.val).card = 2 := by
  have hle : (S.val ∩ T.val).card ≤ 3 := by
    simpa only [S.property] using Finset.card_le_card (Finset.inter_subset_left (s₁ := S.val) (s₂ := T.val))
  constructor
  · rintro ⟨_, k, hk⟩
    omega
  · intro he
    constructor
    · intro heq
      have hi : (S.val ∩ T.val).card = 3 := by simp [heq, T.property]
      omega
    · rcases he with he | he <;> simp [he]

theorem complex_neighbor_card {h : ℕ} (S : Triple h) :
    Fintype.card {T : Triple h // ComplexNeighbor S T} =
      (h - 3).choose 3 + 3 * (h - 3) := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (complex_neighbor_iff S))]
  rw [Fintype.card_subtype_or_disjoint]
  · rw [triple_intersection_card S 0 (by omega), triple_intersection_card S 2 (by omega)]
    simp
  · intro p hp hq T hT
    have h0 := hp T hT
    have h2 := hq T hT
    omega

/-- There is one side wire per ordered pair, not per undirected edge. -/
abbrev BitPairs (h : ℕ) := {p : Triple h × Triple h // BitNeighbor p.1 p.2}
abbrev ComplexPairs (h : ℕ) := {p : Triple h × Triple h // ComplexNeighbor p.1 p.2}

theorem bit_pairs_card (h : ℕ) :
    Fintype.card (BitPairs h) = h.choose 3 * (3 * (h - 3).choose 2) := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (@BitNeighbor h)), Fintype.card_sigma]
  simp [bit_neighbor_card]

theorem complex_pairs_card (h : ℕ) :
    Fintype.card (ComplexPairs h) = h.choose 3 * ((h - 3).choose 3 + 3 * (h - 3)) := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (@ComplexNeighbor h)), Fintype.card_sigma]
  simp [complex_neighbor_card]

theorem triple_card_100 : Fintype.card (Triple 100) = 161700 := by
  rw [triple_card]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem bit_neighbor_card_100 (S : Triple 100) :
    Fintype.card {T : Triple 100 // BitNeighbor S T} = 13968 := by
  rw [bit_neighbor_card]
  norm_num [Nat.choose_two_right]

theorem complex_neighbor_card_100 (S : Triple 100) :
    Fintype.card {T : Triple 100 // ComplexNeighbor S T} = 147731 := by
  rw [complex_neighbor_card]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem bit_pairs_card_100 : Fintype.card (BitPairs 100) = 161700 * 13968 := by
  rw [bit_pairs_card]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem complex_pairs_card_100 : Fintype.card (ComplexPairs 100) = 161700 * 147731 := by
  rw [complex_pairs_card]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- Relabeling a bank transports the actual ordered-pair subtype, so its count
applies to finite-index circuit wires as well as subset-indexed wires. -/
def pairsEquiv {β γ : Type*} (e : β ≃ γ) (P : γ → γ → Prop) :
    {p : β × β // P (e p.1) (e p.2)} ≃ {p : γ × γ // P p.1 p.2} where
  toFun p := ⟨(e p.val.1, e p.val.2), p.property⟩
  invFun p := ⟨(e.symm p.val.1, e.symm p.val.2), by simpa using p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

/-- This predicate is definitionally the circuit's intersection-one `BitPair`. -/
theorem indexed_bit_pairs_card {h n : ℕ} (e : Fin n ≃ Triple h) :
    Fintype.card {p : Fin n × Fin n // ((e p.1).val ∩ (e p.2).val).card = 1} =
      h.choose 3 * (3 * (h - 3).choose 2) := by
  calc
    _ = Fintype.card (BitPairs h) := Fintype.card_congr (pairsEquiv e (@BitNeighbor h))
    _ = _ := bit_pairs_card h

/-- This predicate is definitionally `Circuit.ComplexPair` for the enumerated
labels; disequality and even intersection are both retained in the count. -/
theorem indexed_complex_pairs_card {h n : ℕ} (e : Fin n ≃ Triple h) :
    Fintype.card {p : Fin n × Fin n // (e p.1).val ≠ (e p.2).val ∧
      Even ((e p.1).val ∩ (e p.2).val).card} =
      h.choose 3 * ((h - 3).choose 3 + 3 * (h - 3)) := by
  calc
    _ = Fintype.card (ComplexPairs h) := Fintype.card_congr (pairsEquiv e (@ComplexNeighbor h))
    _ = _ := complex_pairs_card h

end NeighborCounts

end IntegerMultBounds.Networks
