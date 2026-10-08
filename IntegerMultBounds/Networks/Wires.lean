import IntegerMultBounds.Networks.NeighborCounts

/-! Explicit role sets for the full three-coordinate network layout. Each
invocation has its own side and central wires, including across stages. This
counts the named layout; compilation of the global gate schedule and attachment
of its nested labels are separate obligations. -/

namespace IntegerMultBounds.Networks.Wires

open NeighborCounts

abbrev Address (h : ℕ) := Triple h × Triple h × Triple h

/-- A stage and the two fixed coordinates identify one invocation. -/
abbrev Invocation (h : ℕ) := Fin 3 × Triple h × Triple h

abbrev BitRole (h : ℕ) :=
  Address h ⊕ Address h ⊕ (Invocation h × (BitPairs h ⊕ Fin h))

abbrev ComplexRole (h : ℕ) :=
  Address h ⊕ Address h ⊕ (Invocation h × (ComplexPairs h ⊕ Fin (h + 1)))

theorem address_card (h : ℕ) : Fintype.card (Address h) = (h.choose 3) ^ 3 := by
  simp [Address, pow_succ]
  ring

theorem invocation_card (h : ℕ) : Fintype.card (Invocation h) = 3 * (h.choose 3) ^ 2 := by
  simp [Invocation, pow_two]

theorem bit_role_card (h : ℕ) :
    Fintype.card (BitRole h) = 2 * (h.choose 3) ^ 3 +
      (3 * (h.choose 3) ^ 2) * (h.choose 3 * (3 * (h - 3).choose 2) + h) := by
  simp only [BitRole, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    triple_card, bit_pairs_card]
  ring

theorem complex_role_card (h : ℕ) :
    Fintype.card (ComplexRole h) = 2 * (h.choose 3) ^ 3 +
      (3 * (h.choose 3) ^ 2) * (h.choose 3 * ((h - 3).choose 3 + 3 * (h - 3)) + (h + 1)) := by
  simp only [ComplexRole, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    triple_card, complex_pairs_card]
  ring

theorem address_card_100 : Fintype.card (Address 100) = 4227952113000000 := by
  norm_num only [Address, Fintype.card_prod, triple_card_100]

theorem invocation_card_100 : Fintype.card (Invocation 100) = 78440670000 := by
  norm_num only [Invocation, Fintype.card_prod, Fintype.card_fin, triple_card_100]

theorem bit_role_card_100 : Fintype.card (BitRole 100) = 177176569091445000000 := by
  norm_num only [BitRole, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    triple_card_100, bit_pairs_card_100]

theorem complex_role_card_100 :
    Fintype.card (ComplexRole 100) = 1873807244643542670000 := by
  norm_num only [ComplexRole, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    triple_card_100, complex_pairs_card_100]

end IntegerMultBounds.Networks.Wires
