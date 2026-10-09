import IntegerMultBounds.Machine.CompactGadgetReservationHeadersVolume
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersReserved

/-! All synthesized-header setup is absorbed in the actual role volume, with
the certified compact width exponent and no extra chunk-spacing factor. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersBudget
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount)
open CompactGadgetReservationHeadersCaller

def coefficient (c : ℕ) := CompactGadgetReservationHeadersRows.constant c*c+
  32*CompactGadgetReservationHeadersCost.coefficient+2

theorem row_bound (r c : ℕ) (hc : 0 < c) : r ≤ c*rowCount r c := by
  have hb := CompactRowPaddingRound.padded_bounds r c hc
  have he := Nat.div_mul_cancel hb.2.2
  unfold rowCount
  nlinarith

theorem preparation_bound (hs : Fin 6 → List Bool) (s : Shape) (n r c : ℕ) (f : Front)
    (hr : 0 < r) (hc : 0 < c) (hK : 0 < s.chunk) (hd : 0 < s.axes)
    (hG : 0 < s.guard) (hp : 0 < s.payload) (hn : n ≤ s.axes)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i)) :
    CompactGadgetReservationHeadersRows.cost r c+1+headerCost hs r c f+1 ≤
      coefficient c*(rowCount r c*s.recordWidth) := by
  have hrows := CompactGadgetReservationData.rowCount_pos hc hr
  have hrec : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hv7 : ∀ i, Counter.value (headerWords hs r c i) =
      CompactGadgetReservationHeadersSchedule.originalValues s n (rowCount r c) i := by
    intro i; fin_cases i <;> simp [headerWords,CompactGadgetReservationHeadersSchedule.originalValues,
      hv,originals,RecursiveChildQuotientsConstant.bits_value]
  have hc7 : ∀ i, GrowingCounterData.Canonical (headerWords hs r c i) := by
    intro i; fin_cases i <;> simp [headerWords,hcan,RecursiveChildQuotientsConstant.bits_canonical]
  have hh := CompactGadgetReservationHeadersVolume.cost_bound (headerWords hs r c) s n
    (rowCount r c) f hv7 hc7 hrows hK hd hG hp hn
  have hrow := CompactGadgetReservationHeadersRows.cost_linear r c hr hc
  have hrb := row_bound r c hc
  have hrV : r ≤ c*(rowCount r c*s.recordWidth) := by nlinarith
  have htimes := Nat.mul_le_mul_left (CompactGadgetReservationHeadersRows.constant c) hrV
  have hV : 1 ≤ rowCount r c*s.recordWidth := Nat.mul_pos hrows hrec
  unfold coefficient headerCost
  nlinarith

theorem uniform_bound (c : ℕ) (hc : 0 < c) : ∃ C : ℝ, 0 < C ∧
    ∀ (hs : Fin 6 → List Bool) (s : Shape) (n r : ℕ) (f : Front),
    0 < r → 0 < s.chunk → 0 < s.axes → 0 < s.guard → 0 < s.payload → n ≤ s.axes →
    (∀ i, Counter.value (hs i) = originals s n i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    ((CompactGadgetReservationHeadersRows.cost r c+1+headerCost hs r c f+1+
      BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
        (s.width n) (s.gap n f) (s.suffix n)
        (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f) : ℕ) : ℝ) ≤
      C*(rowCount r c*s.recordWidth : ℕ)*((max 1 (n*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := CompactGadgetReservationBudget.uniform_bound
  let K : ℝ := coefficient c
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs s n r f hr hchunk hd hG hp hn hv hcan
  have hload := hbound s n r c f
    (CompactGadgetReservationHeadersEndpoint.headerWords s n (rowCount r c) f)
    hn (CompactGadgetReservationData.rowCount_pos hc hr) hp
    (CompactGadgetReservationHeadersEndpoint.header_values s n (rowCount r c) f)
    (CompactGadgetReservationHeadersEndpoint.header_canonical s n (rowCount r c) f)
  have hprep : ((CompactGadgetReservationHeadersRows.cost r c+1+headerCost hs r c f+1 : ℕ) : ℝ) ≤
      K*(rowCount r c*s.recordWidth : ℕ) := by
    dsimp only [K]
    exact_mod_cast preparation_bound hs s n r c f hr hc hchunk hd hG hp hn hv hcan
  have hw : 1 ≤ ((max 1 (n*s.guard) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*s.guard)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw
    (mul_nonneg hK (by positivity : 0 ≤ ((rowCount r c*s.recordWidth : ℕ) : ℝ)))
  simp only [Nat.cast_add,Nat.cast_one] at hprep ⊢
  nlinarith only [hload,hprep,hm]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersBudget
