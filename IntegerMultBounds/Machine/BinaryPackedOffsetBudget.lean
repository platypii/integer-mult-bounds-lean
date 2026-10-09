import IntegerMultBounds.Machine.BinaryPackedOffsetRun

/-! The actual swap/rotate/swap cost keeps the interchange width exponent.
All power generation, rotations, erasure and sequencing transitions are paid. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetBudget
open BinaryPackedOffsetRun (rotationCost)
open BinaryPackedOffsetData (rows)
open RadixRangePadding (volume)

/-- Physical packed rotation is linear in the full nonempty payload volume. -/
theorem rotation_bound (P w G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    rotationCost P w G B+1 ≤ (FixedBasePowerDescriptor.constant 2+761)*volume P (2^w) G B := by
  have hn : 0 < rows P w G := by unfold rows; positivity
  have hp : 2^w ≤ rows P w G*(2^w*B) :=
    (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_left _ hn)
  have hv : 1 ≤ volume P (2^w) G B := Nat.succ_le_of_lt (by unfold volume; positivity)
  have hm := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2+8) hp
  rw [← BinaryPackedOffsetData.size] at hp hm
  unfold rotationCost
  rw [← BinaryPackedOffsetData.size]
  nlinarith

/-- Uniform width bound for the full physical three-call gadget. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B w : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values P G B w i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    ((2*BinaryRadixEqualShared.cost P G B w hs+rotationCost P w G B+2 : ℕ) : ℝ) ≤
      C*(volume P (2^w) G B : ℝ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedFieldSwap.roundtrip_uniform_bound
  let K : ℝ := (FixedBasePowerDescriptor.constant 2+761 : ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro P G B w hs hP hG hB hv hc
  have hi := hbound P G B w hs hP hG hB hv hc
  have hr : ((rotationCost P w G B+1 : ℕ) : ℝ) ≤ K*(volume P (2^w) G B : ℝ) := by
    dsimp only [K]
    exact_mod_cast rotation_bound P w G B hP hG hB
  have hw : 1 ≤ ((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 w) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hvol : 0 ≤ (volume P (2^w) G B : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hw (mul_nonneg hK hvol)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hi hr ⊢
  nlinarith only [hi,hr,hmul]

end IntegerMultBounds.Machine.BinaryPackedOffsetBudget
