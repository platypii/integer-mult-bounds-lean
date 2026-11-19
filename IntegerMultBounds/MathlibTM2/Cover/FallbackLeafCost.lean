module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPreparedSetup

/-! The stopped leaf pays the interchange rate on its payload volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net]

theorem exchangeTime_leaf_le (U : Type) {d : ℕ} (j i : ℕ) (k t : Fin (d+1)) (width : ℕ) :
    ∃ C : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      exchangeTime U j i k t width w W (Nat.size M) (Nat.size W) ≤
        C*(1+swapVolumeRate w)*(M^(d+1)*W) := by
  obtain ⟨s,setup⟩ := exchangeTime_setup_le U j i k t width
  obtain ⟨a,b,payload⟩ := exchangeTime_le_setup_add_width_volume U j i k t width
  let c := 2*s*(2*(Nat.size prime+1)^2)
  refine ⟨c+a+b,fun w W pos => ?_⟩
  let M := prime^(w+1)
  let V := M^(d+1)*W
  have headers : exchangeTime U j i k t width w 0 (Nat.size M) (Nat.size W) ≤ c*V := by
    apply (setup w _ _).trans
    have field := prefixSetup_volume_le w d
    dsimp only at field
    have bits : Nat.size W ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
    have counter : Nat.size W+1 ≤ 2*W := by omega
    simp only [Nat.add_one_sub_one]
    rw [Nat.mul_assoc s]
    grw [field,counter]
    exact le_of_eq (by dsimp [V,c,M]; ring)
  apply (payload w W (Nat.size M) (Nat.size W)).trans
  change _ + (a*swapVolumeRate w+b)*V ≤ (c+a+b)*(1+swapVolumeRate w)*V
  grw [headers]
  ring_nf
  omega

/-- The constant depends on the selected pairs, independently of atom and suffix width.
The final unit pays for the schedule's terminating instruction. -/
theorem leafScheduleTime_le (U : Type) {d n : ℕ} (j i : Fin n → ℕ)
    (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (xs : List (Fin n)) :
    ∃ C : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      (xs.map fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w W
        (Nat.size M) (Nat.size W)).sum+1 ≤ C*(1+swapVolumeRate w)*(M^(d+1)*W) := by
  choose c hc using fun a => exchangeTime_leaf_le U (j a) (i a) (k a) (t a) (width a)
  refine ⟨(xs.map c).sum+1,fun w W pos => ?_⟩
  let M := prime^(w+1)
  let cost := fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w W (Nat.size M) (Nat.size W)
  let bill := (1+swapVolumeRate w)*(M^(d+1)*W)
  have sum (ys : List (Fin n)) : (ys.map cost).sum ≤ (ys.map c).sum*bill := by
    induction ys with
    | nil => simp
    | cons a ys ih =>
      simp only [List.map_cons,List.sum_cons,Nat.add_mul]
      exact Nat.add_le_add (by simpa only [cost,bill,M,Nat.mul_assoc] using hc a w W pos) ih
  have positive : 0 < prime := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos
  have paid : 0 < bill := by dsimp [bill,M]; positivity
  simpa only [bill,M,Nat.add_mul,Nat.one_mul,Nat.mul_assoc] using Nat.add_le_add (sum xs) paid

/-- Loading the headers, placing the schedule, dropping the pivot and clearing the
private tapes preserve the interchange rate for each fixed caller program. -/
theorem callerLeafTime_le (U : Type) {d n : ℕ} (j i : Fin n → ℕ)
    (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (xs : List (Fin n)) (rank work push : ℕ) :
    ∃ C : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let H := Nat.size M
      let J := Nat.size W
      let cost := (xs.map fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w W H J).sum
      let ticks := 6*(3*H+J+1+w+rank*H)+43+(1+(1+cost+1+(4*H+4)))
      ticks+(4*work+1+work*(6*(push*ticks))) ≤ C*((1+swapVolumeRate w)*(M^(d+1)*W)) := by
  obtain ⟨c,hc⟩ := leafScheduleTime_le U j i k t width xs
  let a := 6*(6+rank)+c+53
  refine ⟨a+(4*work+1)+work*(6*(push*a)),fun w W pos => ?_⟩
  intro M H J cost ticks
  let bill := (1+swapVolumeRate w)*(M^(d+1)*W)
  have pm : 0 < M := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
  have vol : M^(d+1)*W ≤ bill := Nat.le_mul_of_pos_left _ (by omega)
  have m : M ≤ bill := calc
    M ≤ M^d*M := Nat.le_mul_of_pos_left _ (pow_pos pm _)
    _ ≤ M^(d+1)*W := by rw [← pow_succ]; exact Nat.le_mul_of_pos_right _ pos
    _ ≤ bill := vol
  have h : H ≤ bill := (Nat.size_le.mpr Nat.lt_two_pow_self).trans m
  have u : J ≤ bill := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    ((Nat.le_mul_of_pos_left _ (pow_pos pm _)).trans vol)
  have wle : w ≤ bill := (Nat.lt_two_pow_self (n := w)).le.trans
    ((Nat.pow_le_pow_left IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.two_le w).trans
      ((Nat.pow_le_pow_right IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos (Nat.le_succ w)).trans m))
  have unit : 1 ≤ bill := pm.trans_le m
  have scheduled : cost+1 ≤ c*bill := by simpa only [Nat.mul_assoc] using hc w W pos
  have time : ticks ≤ a*bill := by
    dsimp only [ticks,a]
    have scaled := Nat.mul_le_mul_left rank h
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at *
    omega
  change _ ≤ _*bill
  rw [Nat.add_mul,Nat.add_mul]
  have overhead : 4*work+1 ≤ (4*work+1)*bill := Nat.le_mul_of_pos_right _ unit
  grw [time,overhead]
  exact le_of_eq (by ring)

/-- The complete caller execution pays the interchange exponent in the recurrence.
The schedule-only statement is available at 7351c0cd. -/
theorem callerLeafTime_rpow (U : Type) {d n : ℕ} (j i : Fin n → ℕ)
    (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (xs : List (Fin n)) (rank work push : ℕ) :
    ∃ C : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let H := Nat.size M
      let J := Nat.size W
      let cost := (xs.map fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w W H J).sum
      let ticks := 6*(3*H+J+1+w+rank*H)+43+(1+(1+cost+1+(4*H+4)))
      ((ticks+(4*work+1+work*(6*(push*ticks))) : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^(d+1)*W : ℕ) := by
  obtain ⟨c,hc⟩ := callerLeafTime_le U j i k t width xs rank work push
  refine ⟨c*(3808276+M8.RevMachine.LeafCore.C),fun w W pos => ?_⟩
  have rate := swapVolumeRate_le w
  have one : (1 : ℝ) ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
  have bound : (1+swapVolumeRate w : ℕ) ≤ (3808276+M8.RevMachine.LeafCore.C)*
      ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
    simp only [Nat.cast_add,Nat.cast_one] at rate one ⊢
    linarith
  have steps := Nat.cast_le (α := ℝ).mpr (hc w W pos)
  simp only [Nat.cast_mul,← mul_assoc] at steps ⊢
  apply steps.trans
  rw [mul_assoc (c : ℝ) (3808276+M8.RevMachine.LeafCore.C)]
  gcongr

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
