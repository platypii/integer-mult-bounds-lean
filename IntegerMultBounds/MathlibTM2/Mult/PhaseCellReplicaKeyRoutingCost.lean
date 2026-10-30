module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPackedReplicaKeyRouter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyHeaders
public import Mathlib.Tactic.Ring

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

/-- Complete routing from borrowed unary dimensions, including header allocation,
normalization and erasure. The bank stock is measured before header allocation. -/
noncomputable def generatedPackedReplicaKeyRoutingCost (T t₀ W h d stock : ℕ) : ℕ :=
  (21*(W+h+d+2)+56) +
    packedReplicaKeyRoutingCost T t₀ W h d (stock+replicaKeyHeaderVolume W h d)
      (replicaKeyHeaderBits W h d) + (2*replicaKeyHeaderVolume W h d+11)

/-- The existing balanced interchange bound pays the complete actual router,
including generated canonical header *values*. Header generation/erasure itself
is charged separately. This does not assume an arbitrary rectangle is balanced. -/
theorem packedReplicaKeyRoutingCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ W h d stock : ℕ),
      0 < W → h ≤ d+1 → d ≤ h+1 →
      (packedReplicaKeyRoutingCost T t₀ W h d stock (replicaKeyHeaderBits W h d) : ℝ) ≤
        C*(T+12*swapT t₀+5)*(2^h*(2^d*W)) *
          ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau +
        12*stock+50*(2^h*(2^d*W))+4*T+12*swapT t₀+54 := by
  obtain ⟨C,hC,hbound⟩ := swapCost_le
  refine ⟨2*C,by positivity,?_⟩
  intro T t₀ W h d stock hW hhd hdh
  have hv : ∀ i, Counter.value (replicaKeyHeaderBits W h d i) = swapValues 1 1 W h d i := by
    intro i
    exact Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _)
  have hc : ∀ i, GrowingCounterData.Canonical (replicaKeyHeaderBits W h d i) := by
    intro i
    exact binBits_size_canonical _
  have hb := hbound 1 1 W h d (replicaKeyHeaderBits W h d) (by decide) (by decide) hW hhd hdh hv hc
  have hvol : BinaryAdjacentWidthInterchange.volume 1 (2^h) 1 (2^d) W = 2^h*(2^d*W) := by
    simp [BinaryAdjacentWidthInterchange.volume,Nat.mul_assoc]
  rw [hvol] at hb
  rw [packedReplicaKeyRoutingCost_eq]
  have hm := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 2*(T+12*swapT t₀+5) by positivity)
  push_cast at hm ⊢
  nlinarith

/-- The generated lifecycle adds one linear dimension-conversion charge and
fourteen passes over the header volume (normalization plus erasure). -/
theorem generatedPackedReplicaKeyRoutingCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ W h d stock : ℕ),
      0 < W → h ≤ d+1 → d ≤ h+1 →
      (generatedPackedReplicaKeyRoutingCost T t₀ W h d stock : ℝ) ≤
        C*(T+12*swapT t₀+5)*(2^h*(2^d*W)) *
          ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau +
        12*stock+50*(2^h*(2^d*W))+4*T+12*swapT t₀+
        14*replicaKeyHeaderVolume W h d+21*(W+h+d+2)+121 := by
  obtain ⟨C,hC,hbound⟩ := packedReplicaKeyRoutingCost_uniform
  refine ⟨C,hC,?_⟩
  intro T t₀ W h d stock hW hhd hdh
  have hb := hbound T t₀ W h d (stock+replicaKeyHeaderVolume W h d) hW hhd hdh
  unfold generatedPackedReplicaKeyRoutingCost
  push_cast at hb ⊢
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
