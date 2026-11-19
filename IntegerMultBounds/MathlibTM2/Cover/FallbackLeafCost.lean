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

/-- In real-valued recurrence form, the leaf toll has the interchange exponent. -/
theorem leafScheduleTime_rpow (U : Type) {d n : ℕ} (j i : Fin n → ℕ)
    (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (xs : List (Fin n)) :
    ∃ C : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      (((xs.map fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w W
        (Nat.size M) (Nat.size W)).sum+1 : ℕ) : ℝ) ≤
        C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^(d+1)*W : ℕ) := by
  obtain ⟨c,hc⟩ := leafScheduleTime_le U j i k t width xs
  refine ⟨c*(3808276+M8.RevMachine.LeafCore.C),fun w W pos => ?_⟩
  have rate := swapVolumeRate_le w
  have one : (1 : ℝ) ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
  have bound : (1+swapVolumeRate w : ℕ) ≤ (3808276+M8.RevMachine.LeafCore.C)*
      ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
    simp only [Nat.cast_add,Nat.cast_one] at rate one ⊢
    linarith
  have steps := Nat.cast_le (α := ℝ).mpr (hc w W pos)
  simp only [Nat.cast_mul] at steps ⊢
  apply steps.trans
  rw [mul_assoc (c : ℝ) (3808276+M8.RevMachine.LeafCore.C)]
  gcongr

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
