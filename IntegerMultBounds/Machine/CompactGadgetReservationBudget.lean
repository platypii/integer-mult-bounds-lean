import IntegerMultBounds.Machine.CompactGadgetReservationRun
import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalBudget

/-! The actual reserved-front/back movement retains the certified compact
width exponent. Its width is n*G, without the wider selected-slot spacing K. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationBudget
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount)

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (s : Shape) (n r c : ℕ) (f : Front) (hs : Fin 4 → List Bool),
    n ≤ s.axes → 0 < rowCount r c → 0 < s.payload →
    (∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values
      (s.prefixRange (rowCount r c) f) (s.gap n f) (s.suffix n) (s.width n) i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f) (s.suffix n) hs : ℝ) ≤
      C*(rowCount r c*s.recordWidth : ℕ)*((max 1 (n*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  refine ⟨C,hC,?_⟩
  intro s n r c f hs hn hr hp hv hc
  have h := hbound (s.prefixRange (rowCount r c) f) (s.gap n f) (s.suffix n)
    (s.width n) hs (s.prefix_pos _ _ hr) (s.gap_pos n f) (s.suffix_pos n hp) hv hc
  rw [s.rectangle_volume n (rowCount r c) hn f] at h
  exact h

end IntegerMultBounds.Machine.CompactGadgetReservationBudget
