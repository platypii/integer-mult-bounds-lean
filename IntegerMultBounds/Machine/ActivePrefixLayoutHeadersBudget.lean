import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersRun

/-! Every copy, arithmetic pass, power construction, multiplication and
cleanup is bounded linearly by any positive containing volume that bounds
original descriptors and the produced suffix. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget
open ActivePrefixLayoutHeadersData ActivePrefixLayoutHeadersRun ActiveRepairRankHeadersCommands

theorem seeded_bounded (d : Inputs) (A : ℕ) (ho : ∀ i, originalValues d i≤A) :
    Bounded (seeded d) (A+1) := by
  intro i
  by_cases h24 : i=24
  · simp [seeded,put,Function.update,h24]
  · simp only [seeded,put,Function.update_of_ne h24]
    by_cases hi : i.val<14
    · simp only [initial,hi,↓reduceDIte,Option.getD_some]
      exact (ho ⟨i.val,hi⟩).trans (by omega)
    · simp [initial,hi]

theorem schedule_length (mode : Mode) : (schedule mode).length≤20 := by cases mode <;> decide

theorem arithmetic_bound (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) :
    scheduleCost (schedule mode) (seeded d)≤900*3^20*A := by
  have h := scheduleCost_bounded (schedule mode) (seeded d) (A+1) (seeded_bounded d A ho)
  have hp : 3^(schedule mode).length≤3^20 := Nat.pow_le_pow_right (by decide) (schedule_length mode)
  nlinarith

theorem values_le (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix mode d≤A) : ∀ i, values mode d i≤6*A := by
  have h0 := ho 0; have h2 := ho 2; have h3 := ho 3; have h4 := ho 4
  have h5 := ho 5; have h7 := ho 7; have h8 := ho 8; have h9 := ho 9
  have h10 := ho 10; have h11 := ho 11; have h12 := ho 12
  simp [originalValues] at h0 h2 h3 h4 h5 h7 h8 h9 h10 h11 h12
  intro i; fin_cases i <;> cases mode
  all_goals simp [values,prefixWidth,targetStart,sourceStart]
  all_goals omega

theorem exponent_le (mode : Mode) (d : Inputs) (A : ℕ) (ho : ∀ i, originalValues d i≤A) :
    exponent mode d≤3*A := by
  have h0 := ho 0; have h1 := ho 1; have h4 := ho 4
  simp [originalValues] at h0 h1 h4
  cases mode <;> simp only [exponent] <;> omega

theorem power_le (mode : Mode) (d : Inputs) (A : ℕ) (hp : 0<d.payload) (hs : suffix mode d≤A) :
    2^exponent mode d≤A :=
  (Nat.le_mul_of_pos_left _ hp).trans hs

theorem finished_bounded (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix mode d≤A) : Bounded (finished mode d) (6*A) := by
  intro i
  by_cases hi : i.val<14
  · simpa [finished,hi] using (ho ⟨i.val,hi⟩).trans (by omega : A≤6*A)
  · by_cases hj : i.val<24
    · simpa [finished,hi,hj] using values_le mode d A hA ho hs ⟨i.val-14,by omega⟩
    · simp [finished,hi,hj]

theorem multiplied_bounded (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A) (hp : 0<d.payload)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix mode d≤A) : Bounded (multiplied mode d) (6*A) := by
  have he := exponent_le mode d A ho
  have hpow := power_le mode d A hp hs
  intro i
  by_cases h23 : i=23
  · simp [multiplied,put,Function.update,h23]; omega
  by_cases h25 : i=25
  · simp [multiplied,powered,put,Function.update,h25]; omega
  simp only [multiplied,powered,put,Function.update_of_ne h23,Function.update_of_ne h25]
  by_cases hi : i.val<14
  · simpa [arithmetic,hi] using (ho ⟨i.val,hi⟩).trans (by omega : A≤6*A)
  by_cases hj : i.val<23
  · simpa [arithmetic,hi,hj] using values_le mode d A hA ho hs ⟨i.val-14,by omega⟩
  by_cases hk : i.val=24
  · simp [arithmetic,hk]; omega
  · simp [arithmetic,hi,hj,hk]

def constant := 900*3^20+FixedBasePowerDescriptor.constant 2+53+18900+41

theorem cost_bound (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A) (hp : 0<d.payload)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix mode d≤A) : ActivePrefixLayoutHeadersRun.cost mode d≤constant*A := by
  have ha := arithmetic_bound mode d A hA ho
  have hpow := power_le mode d A hp hs
  have ht := scheduleCost_bounded scratchCleanup (multiplied mode d) (6*A)
    (multiplied_bounded mode d A hA hp ho hs)
  have htemp : scheduleCost scratchCleanup (multiplied mode d)≤18900*A := by
    change scheduleCost scratchCleanup (multiplied mode d)≤300*3^2*(6*A+1) at ht
    omega
  have hpower := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hpow
  unfold ActivePrefixLayoutHeadersRun.cost constant
  nlinarith only [ha,htemp,hpower,hs,hA]

def cleanupConstant := 2100*3^10

theorem cleanup_bound (mode : Mode) (d : Inputs) (A : ℕ) (hA : 0<A)
    (ho : ∀ i, originalValues d i≤A) (hs : suffix mode d≤A) : cleanupCost mode d≤cleanupConstant*A := by
  have h := scheduleCost_bounded outputCleanup (finished mode d) (6*A) (finished_bounded mode d A hA ho hs)
  change cleanupCost mode d≤300*3^10*(6*A+1) at h
  unfold cleanupConstant
  nlinarith

end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget
