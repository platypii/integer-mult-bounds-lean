import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersRun

/-! All highest-bit header construction and erasure costs are absorbed into
the original array volume, without a record-width allowance. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersBudget
open ActiveTargetHighestPairData ActiveTargetHighestPairHeadersData
open ActiveRepairRankHeadersCommands

theorem volume_positive (g : Geometry) : 0<volume g := by
  have := g.positiveRows
  have := g.positivePayload
  unfold volume P gap suffix RadixRangePadding.volume
  positivity

theorem factor_bounds (g : Geometry) : P g≤volume g ∧ gap g≤volume g ∧ suffix g≤volume g := by
  have hp : 0<P g := by have := g.positiveRows; unfold P; positivity
  have hg : 0<gap g := by unfold gap; positivity
  have hs : 0<suffix g := by have := g.positivePayload; unfold suffix; positivity
  refine ⟨?_,?_,?_⟩
  · convert Nat.le_mul_of_pos_right (P g) (show 0<4*gap g*suffix g by positivity) using 1
    unfold volume RadixRangePadding.volume
    ring
  · convert Nat.le_mul_of_pos_right (gap g) (show 0<4*P g*suffix g by positivity) using 1
    unfold volume RadixRangePadding.volume
    ring
  · convert Nat.le_mul_of_pos_right (suffix g) (show 0<4*P g*gap g by positivity) using 1
    unfold volume RadixRangePadding.volume
    ring

theorem power_bounds (g : Geometry) : 2^g.L≤volume g ∧ 2^g.K≤volume g := by
  have h := factor_bounds g
  exact ⟨(Nat.le_mul_of_pos_left _ g.positiveRows).trans h.1,
    (Nat.le_mul_of_pos_right _ g.positivePayload).trans h.2.2⟩

theorem originals_bound (g : Geometry) : ∀ i, originalValues g i≤volume g := by
  have h := factor_bounds g
  have he := power_bounds g
  have hr : g.rows≤P g := Nat.le_mul_of_pos_right _ (by positivity)
  have hp : g.payload≤suffix g := Nat.le_mul_of_pos_left _ (by positivity)
  intro i
  fin_cases i
  · exact (Nat.lt_two_pow_self (n := g.L)).le.trans he.1
  · exact (Nat.lt_two_pow_self (n := g.G)).le.trans h.2.1
  · exact (Nat.lt_two_pow_self (n := g.K)).le.trans he.2
  · exact hr.trans h.1
  · exact hp.trans h.2.2

theorem values_bound (g : Geometry) : ∀ i, values g i≤3*volume g := by
  have ho := originals_bound g
  have h0 := ho 0
  have h1 := ho 1
  have h3 := ho 3
  change g.L≤volume g at h0
  change g.G≤volume g at h1
  change g.rows≤volume g at h3
  have hV := volume_positive g
  have hf := factor_bounds g
  intro i
  fin_cases i <;> simp [values,W] <;> omega

theorem seeded_bounded (g : Geometry) : Bounded (seeded g) (volume g) := by
  have hV := volume_positive g
  intro i
  by_cases hi : i=9
  · simp [seeded,put,Function.update,hi]; omega
  · simp only [seeded,put,Function.update_of_ne hi]
    by_cases hj : i.val<5
    · simpa [initial,hj] using originals_bound g ⟨i.val,hj⟩
    · simp [initial,hj]

theorem arithmetic_bounded (g : Geometry) : Bounded (arithmetic g) (3*volume g) := by
  intro i
  by_cases hi : i.val<5
  · simpa [arithmetic,hi] using (originals_bound g ⟨i.val,hi⟩).trans (by omega : volume g≤3*volume g)
  · by_cases hj : i.val<12
    · simpa [arithmetic,hi,hj] using values_bound g ⟨i.val-5,by omega⟩
    · simp [arithmetic,hi,hj]

theorem put_bounded (st : State) (i : Fin 28) (n A : ℕ)
    (h : Bounded st A) (hn : n≤A) : Bounded (put st i n) A := by
  intro j
  by_cases hj : j=i
  · simp [put,Function.update,hj]; exact hn
  · simpa [put,Function.update,hj] using h j

theorem multiplied_bounded (g : Geometry) : Bounded (multipliedB g) (3*volume g) := by
  have hf := factor_bounds g
  have he := power_bounds g
  exact put_bounded _ _ _ _
    (put_bounded _ _ _ _ (put_bounded _ _ _ _ (put_bounded _ _ _ _
      (put_bounded _ _ _ _ (arithmetic_bounded g) (by omega)) (by omega))
      (by omega)) (by omega)) (by omega)

theorem finished_bounded (g : Geometry) : Bounded (finished g) (3*volume g) := by
  intro i
  by_cases hi : i.val<5
  · simpa [finished,hi] using (originals_bound g ⟨i.val,hi⟩).trans (by omega : volume g≤3*volume g)
  · by_cases hj : i.val<15
    · simpa [finished,hi,hj] using values_bound g ⟨i.val-5,by omega⟩
    · simp [finished,hi,hj]

def constant := 600*3^9+3*FixedBasePowerDescriptor.constant 2+106+1200*3^2+72
def cleanupConstant := 1200*3^10

theorem cost_bound (g : Geometry) : ActiveTargetHighestPairHeadersRun.cost g≤constant*volume g := by
  have ha := scheduleCost_bounded arithmeticSchedule (seeded g) (volume g) (seeded_bounded g)
  have hs := scheduleCost_bounded scratchCleanup (multipliedB g) (3*volume g) (multiplied_bounded g)
  change scheduleCost arithmeticSchedule (seeded g)≤300*3^9*(volume g+1) at ha
  change scheduleCost scratchCleanup (multipliedB g)≤300*3^2*(3*volume g+1) at hs
  have hf := factor_bounds g
  have he := power_bounds g
  have hG := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hf.2.1
  have hL := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) he.1
  have hK := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) he.2
  have hV := volume_positive g
  unfold ActiveTargetHighestPairHeadersRun.cost constant
  nlinarith only [ha,hs,hG,hL,hK,hf.1,hf.2.2,hV]

theorem cleanup_bound (g : Geometry) : ActiveTargetHighestPairHeadersRun.cleanupCost g≤cleanupConstant*volume g := by
  have h := scheduleCost_bounded outputCleanup (finished g) (3*volume g) (finished_bounded g)
  change ActiveTargetHighestPairHeadersRun.cleanupCost g≤300*3^10*(3*volume g+1) at h
  have hV := volume_positive g
  unfold cleanupConstant
  nlinarith

end IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersBudget
