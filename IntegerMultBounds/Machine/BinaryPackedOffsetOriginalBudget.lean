import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalRun
import IntegerMultBounds.Machine.BinaryPackedOffsetBudget

/-! Original-header fiber-count construction and erasure preserve the
certified interchange exponent in the complete physical action. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetOriginalBudget
open BinaryPackedOffsetOriginalRun (cost)
open RadixRangePadding (volume)

 theorem preparation_bound (P w G B : ℕ) (hP : 0<P) (hG : 0<G) (hB : 0<B) :
    BinaryPackedRowCountBudget.cost P w G +
      (2*(BinaryPackedRowCount.rowBits P w G).length+4)+2 ≤
    (FixedBasePowerDescriptor.constant 2+195)*volume P (2^w) G B := by
  have hp := BinaryPackedRowCountBudget.bound P w G hP hG
  have hc := BinaryPackedRowCountBudget.cleanup_bound P w G
  have hr : P*2^w*G ≤ volume P (2^w) G B := by
    have hn : 0<2^w*B := by positivity
    have hh := Nat.le_mul_of_pos_right (P*2^w*G) hn
    simpa only [BinaryPackedOffsetData.rows,BinaryPackedOffsetData.size] using hh
  have hv : 1 ≤ volume P (2^w) G B := Nat.succ_le_of_lt (by unfold volume; positivity)
  have hm := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2+112) hr
  nlinarith

 theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (P G B w : ℕ) (hs : Fin 4 → List Bool),
    0<P → 0<G → 0<B →
    (∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values P G B w i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    ((cost P w G B hs : ℕ) : ℝ) ≤
      C*(volume P (2^w) G B : ℝ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetBudget.uniform_bound
  let K : ℝ := (FixedBasePowerDescriptor.constant 2+195 : ℕ)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro P G B w hs hP hG hB hv hc
  have hi := hbound P G B w hs hP hG hB hv hc
  have hp : ((BinaryPackedRowCountBudget.cost P w G+
      (2*(BinaryPackedRowCount.rowBits P w G).length+4)+2 : ℕ) : ℝ) ≤
      K*(volume P (2^w) G B : ℝ) := by
    dsimp only [K]
    exact_mod_cast preparation_bound P w G B hP hG hB
  have hw : 1≤((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 w) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hK (by positivity : 0≤(volume P (2^w) G B : ℝ)))
  unfold cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hi hp ⊢
  nlinarith only [hi,hp,hm]
end IntegerMultBounds.Machine.BinaryPackedOffsetOriginalBudget
