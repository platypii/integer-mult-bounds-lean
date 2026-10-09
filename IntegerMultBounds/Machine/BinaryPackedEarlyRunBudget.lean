import IntegerMultBounds.Machine.BinaryPackedEarlyRun
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixLoadBudget

/-! The complete four actual loads retain a uniform common-volume bound and
the certified interchange exponent. Both output-width setup allowances are
explicitly absorbed by the physical suffixes of the same reservation. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRunBudget
open CompactGadgetReservationShape
open BinaryPackedEarlyGeometry
open BinaryPackedEarlyRunBank (gapHeaders prefixHeaders)
open BinaryPackedEarlyRunGap (values firstCost thirdCost)
open BinaryPackedEarlyRunPrefix (secondCost fourthCost)

 theorem uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (s : Shape) (q b n rows : ℕ) (_hq : n*q≤s.H) (_hw : n*b≤s.H)
      (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
      (hb : 1≤b) (hbq : b+1≤q),
      0<rows → 0<s.payload → Z.length=n →
      (∀ i, Counter.value (hs i)=values s q b n rows i) →
      (∀ i, GrowingCounterData.Canonical (hs i)) →
      (∀ i, Counter.value (st i)=BinaryRadixRangePrepare.values rows (tempGap s q b n) (suffix s (n*q)) (n*q) i) →
      (∀ i, GrowingCounterData.Canonical (st i)) →
      (∀ i, Counter.value (sc i)=BinaryRadixRangePrepare.values (controlPrefix s q n rows) (controlGap s b n) (suffix s (n*b)) (n*b) i) →
      (∀ i, GrowingCounterData.Canonical (sc i)) →
      BinaryPackedEarlyPrefixBudget.allowance q b n≤suffix s (n*q) →
      BinaryPackedEarlyPrefixBudget.allowance q b n≤suffix s (n*b) →
      ((BinaryPackedEarlyRun.cost s q b n rows st sc hs Z hb hbq : ℕ) : ℝ)≤
        C*(rows*s.recordWidth : ℕ)*((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C1,hC1,bound1⟩ := BinaryRepeatedOffsetLoadBudget.selected_uniform_bound
  obtain ⟨C2,hC2,bound2⟩ := BinaryPackedEarlyPrefixLoadBudget.parity_uniform_bound
  obtain ⟨C3,hC3,bound3⟩ := BinaryRepeatedOffsetLoadBudget.correction_uniform_bound
  obtain ⟨C4,hC4,bound4⟩ := BinaryPackedEarlyPrefixLoadBudget.negative_uniform_bound
  refine ⟨C1+C2+C3+C4+3,by positivity,?_⟩
  intro s q b n rows hq hw st sc hs Z hb hbq hr hp hZ hv hc hst hct hsc hcc hat hac
  have hH : 0<targetTail s q n := by unfold targetTail; positivity
  have hL : 0<controlGap s b n := by unfold controlGap tempTail middle; positivity
  have hBt : 0<suffix s (n*q) := by unfold suffix; positivity
  have hBc : 0<suffix s (n*b) := by unfold suffix; positivity
  have h1 := bound1 (gapHeaders hs) Z st q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q))
    hb hbq hr hH hL hBt (hv 5) (hc 5) hat hst hct
  have h2 := bound2 (prefixHeaders hs) sc q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b))
    hb hbq hr hH hL hBc (hv 6) (hv 3) (hc 6) (hc 3) hac hsc hcc
  have h3 := bound3 (gapHeaders hs) Z st q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q))
    hb hbq hZ hr hH hL hBt (hv 5) (hc 5) hat hst hct
  have h4 := bound4 (prefixHeaders hs) Z sc q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b))
    hb hbq hr hH hL hBc (hv 6) (hv 3) (hc 6) (hc 3) hac hsc hcc
  change ((firstCost s q b n rows st hs Z hb hbq : ℕ) : ℝ)≤
    C1*(RadixRangePadding.volume rows (2^(n*q)) (tempGap s q b n) (suffix s (n*q)) : ℕ)*
      ((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau at h1
  change ((thirdCost s q b n rows st hs Z hb hbq : ℕ) : ℝ)≤
    C3*(RadixRangePadding.volume rows (2^(n*q)) (tempGap s q b n) (suffix s (n*q)) : ℕ)*
      ((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau at h3
  change ((secondCost s q b n rows sc hs hb hbq : ℕ) : ℝ)≤
    C2*(RadixRangePadding.volume (controlPrefix s q n rows) (2^(n*b)) (controlGap s b n) (suffix s (n*b)) : ℕ)*
      ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau at h2
  change ((fourthCost s q b n rows sc hs Z hb hbq : ℕ) : ℝ)≤
    C4*(RadixRangePadding.volume (controlPrefix s q n rows) (2^(n*b)) (controlGap s b n) (suffix s (n*b)) : ℕ)*
      ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau at h4
  rw [temp_volume s q b n rows hq hw] at h1 h3
  rw [control_volume s q b n rows hq hw] at h2 h4
  have hpw : ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau≤((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast max_le_max_left 1 (Nat.mul_le_mul_left n (by omega : b≤q)))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have h2' := h2.trans (mul_le_mul_of_nonneg_left hpw (by positivity : 0≤C2*(rows*s.recordWidth : ℕ)))
  have h4' := h4.trans (mul_le_mul_of_nonneg_left hpw (by positivity : 0≤C4*(rows*s.recordWidth : ℕ)))
  have hvol : 1≤(rows*s.recordWidth : ℕ) := Nat.succ_le_of_lt (by unfold Shape.recordWidth; positivity)
  have hvol' : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by exact_mod_cast hvol
  have hpow : (1 : ℝ)≤((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*q)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hpaid : (1 : ℝ)≤(rows*s.recordWidth : ℕ)*((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau :=
    one_le_mul_of_one_le_of_one_le hvol' hpow
  unfold BinaryPackedEarlyRun.cost
  simp only [Nat.cast_add,Nat.cast_ofNat]
  nlinarith only [h1,h2',h3,h4',hpaid]

end IntegerMultBounds.Machine.BinaryPackedEarlyRunBudget
