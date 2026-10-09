import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedVolume
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReserved

/-! All synthesized-header setup is absorbed in the actual role volume, with
the certified compact width exponent and no extra chunk-spacing factor. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedBudget
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationData (rowCount)
open CompactGadgetReservationHeadersCarvedCaller (headerCost)
open CompactGadgetReservationHeadersCaller (originals headerWords)
open CompactGadgetReservationHeadersCarvedData

def coefficient (c : ℕ) := CompactGadgetReservationHeadersRows.constant c*c+
  31*CompactGadgetReservationHeadersCost.coefficient+84

theorem preparation_bound (hs : Fin 6 → List Bool) (s : Shape) (n b r c : ℕ) (f : Front)
    (hr : 0 < r) (hc : 0 < c) (hK : 0 < s.chunk) (hd : 0 < s.axes)
    (hG : 0 < s.guard) (hp : 0 < s.payload) (hw : n*b ≤ s.H)
    (hv : ∀ i, Counter.value (hs i) = originals s n i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i)) :
    CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+headerCost hs r c (n*b) f+1 ≤
      coefficient c*(rowCount r c*s.recordWidth) := by
  have hrows := CompactGadgetReservationData.rowCount_pos hc hr
  have hrec : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hv7 : ∀ i, Counter.value (headerWords hs r c i) =
      CompactGadgetReservationHeadersCarvedSchedule.originalValues s n (rowCount r c) i := by
    intro i; fin_cases i <;> simp [headerWords,CompactGadgetReservationHeadersCarvedSchedule.originalValues,
      hv,originals,RecursiveChildQuotientsConstant.bits_value]
  have hc7 : ∀ i, GrowingCounterData.Canonical (headerWords hs r c i) := by
    intro i; fin_cases i <;> simp [headerWords,hcan,RecursiveChildQuotientsConstant.bits_canonical]
  have hh := CompactGadgetReservationHeadersCarvedVolume.cost_bound (headerWords hs r c) s n
    (rowCount r c) (n*b) f hv7 hc7 hrows hK hd hG hp hw
  have hrow := CompactGadgetReservationHeadersRows.cost_linear r c hr hc
  have hrb := CompactGadgetReservationHeadersBudget.row_bound r c hc
  have hrV : r ≤ c*(rowCount r c*s.recordWidth) := by nlinarith
  have htimes := Nat.mul_le_mul_left (CompactGadgetReservationHeadersRows.constant c) hrV
  have hV : 1 ≤ rowCount r c*s.recordWidth := Nat.mul_pos hrows hrec
  have hwidth : n*b ≤ rowCount r c*s.recordWidth := by
    have hh : s.H ≤ s.bits := by unfold Shape.bits; omega
    have hb := (Nat.lt_pow_self (n := s.bits) (by decide : 1 < 2)).le
    have hpow := Nat.le_mul_of_pos_right (2^s.bits) hp
    have hrmul := Nat.le_mul_of_pos_left s.recordWidth hrows
    change s.recordWidth ≤ rowCount r c*s.recordWidth at hrmul
    change 2^s.bits ≤ s.recordWidth at hpow
    exact hw.trans (hh.trans (hb.trans (hpow.trans hrmul)))
  unfold coefficient headerCost
  nlinarith

theorem uniform_bound (c : ℕ) (hc : 0 < c) : ∃ C : ℝ, 0 < C ∧
    ∀ (hs : Fin 6 → List Bool) (s : Shape) (n b r : ℕ) (f : Front),
    0 < r → 0 < s.chunk → 0 < s.axes → 0 < s.guard → 0 < s.payload → n*b ≤ s.H →
    (∀ i, Counter.value (hs i) = originals s n i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    ((CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+headerCost hs r c (n*b) f+1+
      BinaryPackedOffsetOriginalRun.cost (s.prefixRange (rowCount r c) f)
        (n*b) (gap s (n*b) f) (suffix s (n*b))
        (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f) : ℕ) : ℝ) ≤
      C*(rowCount r c*s.recordWidth : ℕ)*((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let K : ℝ := coefficient c
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs s n b r f hr hchunk hd hG hp hw hv hcan
  have hload := hbound (s.prefixRange (rowCount r c) f) (gap s (n*b) f) (suffix s (n*b)) (n*b)
    (CompactGadgetReservationHeadersCarvedRouting.headerWords s (rowCount r c) (n*b) f)
    (s.prefix_pos _ f (CompactGadgetReservationData.rowCount_pos hc hr)) (gap_pos s (n*b) f)
    (suffix_pos s (n*b) hp)
    (CompactGadgetReservationHeadersCarvedRouting.header_values s (rowCount r c) (n*b) f)
    (CompactGadgetReservationHeadersCarvedRouting.header_canonical s (rowCount r c) (n*b) f)
  rw [rectangle_volume s (n*b) (rowCount r c) hw f] at hload
  have hprep : ((CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+headerCost hs r c (n*b) f+1 : ℕ) : ℝ) ≤
      K*(rowCount r c*s.recordWidth : ℕ) := by
    dsimp only [K]
    exact_mod_cast preparation_bound hs s n b r c f hr hc hchunk hd hG hp hw hv hcan
  have hw : 1 ≤ ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw
    (mul_nonneg hK (by positivity : 0 ≤ ((rowCount r c*s.recordWidth : ℕ) : ℝ)))
  simp only [Nat.cast_add,Nat.cast_one] at hprep ⊢
  nlinarith only [hload,hprep,hm]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedBudget
