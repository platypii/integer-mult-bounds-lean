import IntegerMultBounds.Networks.GlobalLabels
import IntegerMultBounds.Networks.SignedProjection
import IntegerMultBounds.Parameters

/-! Terminal dimension accounting on the actual physical global wire layout.
The rank inequalities here consume the genuine trace balance and loss bound;
proving those for the complete schedule remains a separate obligation. -/

namespace IntegerMultBounds.Networks.NetworkBudget

open scoped TensorProduct
open Module GlobalLabels

section Terminals
variable {K F B A C : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]
  (D : LinearMap.BilinForm K F) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

omit [FiniteDimensional K F] in
include ht in
theorem terminal_finrank (b : GlobalCircuit.Address B) : finrank K (terminal (K := K) t b) = 1 := by
  apply finrank_span_singleton
  intro hz
  have he : TensorSubspace.form D (TensorSubspace.form D D)
      (t b.1 ⊗ₜ[K] (t b.2.1 ⊗ₜ[K] t b.2.2))
      (t b.1 ⊗ₜ[K] (t b.2.1 ⊗ₜ[K] t b.2.2)) ≠ 0 := by
    simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
      mul_ne_zero (mul_ne_zero (ht b.2.2) (ht b.2.1)) (ht b.1)
  exact he (by rw [hz]; simp)

theorem ambient_finrank : finrank K (StageLabels.Ambient K F) = (finrank K F) ^ 3 := by
  simp only [StageLabels.Ambient, Module.finrank_tensorProduct]
  ring

include hn ht in
theorem complement_finrank (b : GlobalCircuit.Address B) :
    finrank K ((TensorSubspace.form D (TensorSubspace.form D D)).orthogonal (terminal (K := K) t b)) =
      (finrank K F) ^ 3 - 1 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (Labels.tmul_nondegenerate D (TensorSubspace.form D D) hn (Labels.tmul_nondegenerate D D hn hn)),
    terminal_finrank D t ht, ambient_finrank]

include hn ht in
theorem complement_finrank_add_one (b : GlobalCircuit.Address B) :
    finrank K ((TensorSubspace.form D (TensorSubspace.form D D)).orthogonal (terminal (K := K) t b)) + 1 =
      (finrank K F) ^ 3 := by
  have hle := Submodule.finrank_le (terminal (K := K) t b)
  rw [terminal_finrank D t ht, ambient_finrank] at hle
  rw [complement_finrank D hn t ht, Nat.sub_add_cancel hle]

variable [Fintype B] [Fintype A] [Fintype C]

omit [FiniteDimensional K F] in
include ht in
/-- Sum the actual tensor-line source dimensions over the physical X bank. -/
theorem source_total :
    RankTrace.total (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      (source (A := A) (C := C) t) = Fintype.card B ^ 3 := by
  have hp (i : GlobalCircuit.World B A C) :
      finrank K (source (K := K) t i) =
        Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun _ => 0)) i := by
    rcases i with x | y | z
    · exact terminal_finrank D t ht x
    · exact _root_.finrank_bot K _
    · exact _root_.finrank_bot K _
  unfold RankTrace.total
  simp_rw [hp]
  simp [GlobalCircuit.World, GlobalCircuit.Address, pow_succ]
  ring

include hn ht in
/-- Whole-space scratch sinks and complementary Y sinks account for every
physical wire. The additive identity also handles an empty data bank. -/
theorem sink_total :
    RankTrace.total (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      (sink (A := A) (C := C) D t) + Fintype.card B ^ 3 =
      Fintype.card (GlobalCircuit.World B A C) * (finrank K F) ^ 3 := by
  have hsum : (∑ b : GlobalCircuit.Address B,
      finrank K ((TensorSubspace.form D (TensorSubspace.form D D)).orthogonal (terminal (K := K) t b))) +
      Fintype.card (GlobalCircuit.Address B) =
        Fintype.card (GlobalCircuit.Address B) * (finrank K F) ^ 3 := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun b _ => complement_finrank_add_one D hn t ht b)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one] using hh
  have hb : Fintype.card (GlobalCircuit.Address B) = Fintype.card B ^ 3 := by
    simp [GlobalCircuit.Address]
    ring
  have hp (i : GlobalCircuit.World B A C) :
      finrank K (sink D t i) = Sum.elim (fun _ => (finrank K F) ^ 3)
        (Sum.elim (fun b => finrank K ((TensorSubspace.form D (TensorSubspace.form D D)).orthogonal
          (terminal (K := K) t b))) (fun _ => (finrank K F) ^ 3)) i := by
    rcases i with x | y | z
    · change finrank K (⊤ : Submodule K (StageLabels.Ambient K F)) = _
      rw [_root_.finrank_top, ambient_finrank]
      rfl
    · rfl
    · change finrank K (⊤ : Submodule K (StageLabels.Ambient K F)) = _
      rw [_root_.finrank_top, ambient_finrank]
      rfl
  unfold RankTrace.total
  simp_rw [hp]
  simp only [GlobalCircuit.World, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fintype.card_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← hb]
  nlinarith [hsum]

end Terminals

/-- The ordinary label-rank balance yields the complex interface budget. -/
theorem phase_budget {s W m N L ℓ : ℕ}
    (hbalance : s + N + N = W * m + 2 * ℓ) (hloss : ℓ ≤ L) (hroom : 2 * N ≤ W * m) :
    s ≤ W * m - 2 * N + 2 * L := by omega

/-- Rational negative sources add precisely the source dimension to the
ordinary trace rank, including any skipped initial repeated labels. -/
theorem shear_budget {s W m N L ℓ : ℕ}
    (hbalance : s + N + N = W * m + 2 * ℓ) (hloss : ℓ ≤ L) :
    s + N ≤ W * m - N + 2 * L := by omega

/-- The improved complex witness has room for the actual local loss estimate.
This connects the generic budget arithmetic to the already checked parameter
certificate, without asserting that the global trace has yet been assembled. -/
theorem complex_budget_25 {s ℓ : ℕ}
    (hbalance : s + 12167000000 + 12167000000 = 58645352620000 * 15625 + 2 * ℓ)
    (hloss : ℓ ≤ 3 * 2300 ^ 2 * 26 * 25) : s ≤ 916333630984500000 := by
  have hh := phase_budget hbalance hloss (by norm_num)
  norm_num at hh
  exact hh

/-- The numeric role count is the cardinality of the existing physical layout. -/
theorem complex_role_card_25 : Fintype.card (Wires.ComplexRole 25) = 58645352620000 := by
  rw [Wires.complex_role_card, show Nat.choose 25 3 = 2300 by decide,
    show Nat.choose (25 - 3) 3 = 1540 by decide]
  norm_num

/-- Source counting specialized to the actual improved complex motif's labels. -/
theorem complex_source_total_25 :
    RankTrace.total (fun U : Submodule (ZMod 2) (Labels.Cube (ZMod 2) 25) => finrank (ZMod 2) U)
      (source (A := NeighborCounts.ComplexPairs 25) (C := Fin 26)
        (fun T : NeighborCounts.Triple 25 => Labels.indicator (R := ZMod 2) T.val)) = 12167000000 := by
  rw [source_total (Labels.binary 25) _ (by
    intro T
    rw [Labels.binary_self T.val T.property]
    exact one_ne_zero)]
  rw [NeighborCounts.triple_card, show Nat.choose 25 3 = 2300 by decide]
  norm_num

/-- The exact sum of actual sink-label dimensions, not an assigned wire weight. -/
theorem complex_sink_total_25 :
    RankTrace.total (fun U : Submodule (ZMod 2) (Labels.Cube (ZMod 2) 25) => finrank (ZMod 2) U)
      (sink (A := NeighborCounts.ComplexPairs 25) (C := Fin 26) (Labels.binary 25)
        (fun T : NeighborCounts.Triple 25 => Labels.indicator (R := ZMod 2) T.val)) + 12167000000 =
      58645352620000 * 15625 := by
  have hh := sink_total (A := NeighborCounts.ComplexPairs 25) (C := Fin 26)
    (Labels.binary 25) Labels.binary_nondegenerate
    (fun T : NeighborCounts.Triple 25 => Labels.indicator (R := ZMod 2) T.val) (by
      intro T
      rw [Labels.binary_self T.val T.property]
      exact one_ne_zero)
  have hw : Fintype.card (GlobalCircuit.World (NeighborCounts.Triple 25)
      (NeighborCounts.ComplexPairs 25) (Fin 26)) = 58645352620000 := by
    simp only [GlobalCircuit.World, GlobalCircuit.Address, GlobalCircuit.Invocation,
      Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, NeighborCounts.triple_card,
      NeighborCounts.complex_pairs_card]
    rw [show Nat.choose 25 3 = 2300 by decide, show Nat.choose (25 - 3) 3 = 1540 by decide]
  rw [hw, NeighborCounts.triple_card, show Nat.choose 25 3 = 2300 by decide] at hh
  norm_num at hh ⊢
  exact hh

/-- Once the global trace budget is established, its branching ratio meets
the selected complex exponent without any further numerical hypothesis. -/
theorem complex_branching_of_balance {s ℓ : ℕ}
    (hbalance : s + 12167000000 + 12167000000 = 58645352620000 * 15625 + 2 * ℓ)
    (hloss : ℓ ≤ 3 * 2300 ^ 2 * 26 * 25) :
    (s : ℝ) / 58645352620000 < (15625 : ℝ) ^ Parameters.sigma := by
  have hs : (s : ℝ) ≤ 916333630984500000 := by exact_mod_cast complex_budget_25 hbalance hloss
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hs (by norm_num)) Parameters.complex_branching_bound

end IntegerMultBounds.Networks.NetworkBudget
