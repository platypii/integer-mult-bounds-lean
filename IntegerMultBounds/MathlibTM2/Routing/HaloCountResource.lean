module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedVolume

/-! Metadata product construction is charged per complete local field. Each
count product omits the selected width, retaining the manuscript's 1/L saving. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloCountResource
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  RetainedHaloTensor HaloAxisSchedule HaloMixedOrder RetainedTensorEnumeration HaloMixedVolume
variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem packet_cost_eq (V : ℕ) (xs : List ℕ) :
    DimensionProductPacket.cost V xs = xs.length*(31*xs.prod+19*V+57)+19*V+35 := by
  unfold DimensionProductPacket.cost DimensionProductPrepare.cost DimensionProduct.cost readUnaryDimensionCost
  ring

theorem packet_cost_le (V : ℕ) (xs : List ℕ) (D Q : ℕ) (hD : xs.length ≤ D) (hQ : xs.prod ≤ Q) :
    DimensionProductPacket.cost V xs ≤ D*(31*Q+19*V+57)+19*V+35 := by
  rw [packet_cost_eq]
  have hh := Nat.mul_le_mul hD (show 31*xs.prod+19*V+57 ≤ 31*Q+19*V+57 by omega)
  omega

theorem counts_cost_le (V : ℕ) (xs ys zs : List ℕ) (D Q : ℕ)
    (hD : xs.length ≤ D ∧ ys.length ≤ D ∧ zs.length ≤ D)
    (hQ : xs.prod ≤ Q ∧ ys.prod ≤ Q ∧ zs.prod ≤ Q) :
    HaloMixedCountHeaders.cost V xs ys zs ≤ 3*(D*(31*Q+19*V+57)+19*V+35) := by
  have hx := packet_cost_le V xs D Q hD.1 hQ.1
  have hy := packet_cost_le V ys D Q hD.2.1 hQ.2.1
  have hz := packet_cost_le V zs D Q hD.2.2 hQ.2.2
  dsimp only [HaloMixedCountHeaders.cost]
  omega

omit [Fintype ι] in
theorem factor_lengths (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) :
    (xs axis retained s).length ≤ 2*(s.left++s.i::s.right).length ∧
    (ys axis retained s).length ≤ 2*(s.left++s.i::s.right).length ∧
    (zs axis retained s).length ≤ 2*(s.left++s.i::s.right).length := by
  simp only [xs,ys,zs,haloBefore,moveBefore,moveMiddle,List.length_map,List.length_append,List.length_cons]
  omega

theorem counts_cost_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hi : s.i ∉ retained) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) :
    HaloMixedCountHeaders.cost s.params.V (xs axis retained s) (ys axis retained s) (zs axis retained s) ≤
      3*(2*(s.left++s.i::s.right).length*(31*((2*volume axis ∅)/L)+19*s.params.V+57)+19*s.params.V+35) :=
  counts_cost_le s.params.V _ _ _ _ _ (factor_lengths axis retained s)
    (count_products_global_le axis retained s hn hall hi L H hL hH hLpos hlarge)

end IntegerMultBounds.MathlibTM2.Routing.HaloCountResource
