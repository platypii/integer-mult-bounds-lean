module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.M8.StoppedRecurrence

/-! Fixed-atom recursion for the selected bit word, including the bad label classes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open Layer.SelectedMoments

open Networks.Shared50ModularControl (prime)
open Cover.Fallback Cover

open scoped Classical in
/-- Even charging every bad physical record the full fallback child count,
one request spends at most its share of the recurrence's fallback allowance. -/
theorem fallbackRequestWeight (w r parents : ℕ) (hr : r ≤ 64) (P : LabelPadding.Label 64 (w+1))
    (g : Matrix (Fin 64) (Fin 64) (ZMod prime)) (unit : g.det ≠ 0)
    (good : ∀ k (hk : k < r), (GoodForm.lead (k+1) (lt_of_lt_of_le hk hr)
      (g * (LabelRing.res prime (w+1) (by omega)).mapMatrix P * g⁻¹)).det ≠ 0) :
    let records := parents*(prime^(w+1))^(64*64)
    let bad := (List.range records).countP (fun j => fallbackBit hr P (physicalLabel 64 (w+1) j))
    ((32*64^2 : ℝ)*bad)/records ≤ 1/(2^25*2^24) := by
  intro records bad
  have count := fallbackRecordCount w r parents hr P g unit good
  change bad*prime ≤ _*records at count
  have degree : (∑ k ∈ Finset.range r, (k+1)*(64+1)) ≤ 64*(64*65) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range r, (64*65) := Finset.sum_le_sum fun k hk =>
        Nat.mul_le_mul_right 65 ((Finset.mem_range.mp hk).trans_le hr)
      _ ≤ _ := by simp; omega
  have budget : 2^25*2^24*(32*64^2)*(64*(64*65)) ≤ prime := by
    apply le_trans (by decide : _ ≤ 2^100)
    exact (Networks.two_pow_le_coefficientBound (Networks.le_coefficientExponent
      ((by decide : 100 ≤ 53000).trans Nat.lt_two_pow_self.le))).trans
      Networks.Shared50ModularControl.coefficientBound_lt_prime.le
  by_cases empty : records = 0
  · simp [empty]
  have paid := count.trans (Nat.mul_le_mul_right records degree)
  have scaled := Nat.mul_le_mul_left (2^25*2^24*(32*64^2)) paid
  have cap := Nat.mul_le_mul_right records budget
  have total : (2^25*2^24*(32*64^2)*bad)*prime ≤ records*prime := by
    calc
      _ = (2^25*2^24*(32*64^2))*(bad*prime) := by ring
      _ ≤ _ := scaled
      _ = _ := Nat.mul_assoc _ _ _ |>.symm
      _ ≤ prime*records := cap
      _ = _ := Nat.mul_comm _ _
  have raw := Nat.le_of_mul_le_mul_right total Networks.Shared50ModularControl.prime_prime.pos
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero empty) (by norm_num)).2
  push_cast at *
  exact_mod_cast (show 32*64^2*bad*(2^25*2^24) ≤ 1*records by
    convert raw using 1 <;> ring)

/-- Sum the per-request allowance on the actual five-class occurrence list. -/
theorem fallbackScheduleWeight (mass : Fin nodeChildren5.length → ℝ)
    (each : ∀ i, mass i ≤ 1/(2^25*2^24)) : ∑ i, mass i ≤ 1/2^25 := by
  have length := (nodeChildren5_realizes.map (fun _ => (1 : ℕ))).sum_eq
  rw [sum_map_expand] at length
  have count : nodeChildren5.length ≤ 2^24 := by
    simpa using length.le.trans (by decide : (fiveHistogram.map (fun e => e.2 • (1 : ℕ))).sum ≤ 2^24)
  calc
    _ ≤ ∑ _i : Fin nodeChildren5.length, (1 : ℝ)/(2^25*2^24) := Finset.sum_le_sum fun i _ => each i
    _ = (nodeChildren5.length : ℝ) / (2^25*2^24) := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      have bound : (nodeChildren5.length : ℝ) ≤ 2^24 := by exact_mod_cast count
      linarith

/-- Leave half the certified moment gap for fallback children and half for
the fixed-atom route toll. The child sizes here count atoms. -/
theorem coverStoppedCost {Node : Type*} (atoms : Node → ℕ) (bad : Node → ℕ)
    (next : (x : Node) → Fin nodeChildren5.length ⊕ Fin (bad x) → Node)
    (badRank : (x : Node) → Fin (bad x) → ℕ) (badWeight : (x : Node) → Fin (bad x) → ℝ)
    (cost : Node → ℝ) (u : ℕ) {C L : ℝ} (hc : 0 ≤ C) (hl : 0 ≤ L)
    (pos : ∀ x, 1 ≤ atoms x) (leaf : ∀ x, atoms x < u → cost x ≤ C*L) :
    let rank := fun x => Sum.elim (fun i : Fin nodeChildren5.length => nodeChildren5[i.val]) (badRank x)
    let weight := fun x => Sum.elim (fun _ : Fin nodeChildren5.length => 1/(142080 : ℝ)) (badWeight x)
    (∀ x i, 0 ≤ badWeight x i) →
    (∀ x, u ≤ atoms x → ∀ i, badRank x i < 64) →
    (∀ x, u ≤ atoms x → ∀ i, (atoms (next x i) : ℝ) ≤ ((rank x i : ℝ)/64)*atoms x) →
    (∀ x, u ≤ atoms x → ∑ i, badWeight x i*((badRank x i : ℝ)/64)^(1-bitSaving) ≤ 1/2^25) →
    (∀ x, u ≤ atoms x → cost x ≤ (∑ i, weight x i*cost (next x i))+C*atoms x+C*L) →
    ∀ x, cost x ≤ (2^25*C)*atoms x+(2^25*C)*((atoms x : ℝ)^(1-bitSaving)*L) := by
  intro rank weight nonneg badSmall scale fallback node
  have small (x) (hx : u ≤ atoms x) (i) : rank x i < 64 := by
    cases i with
    | inl i => exact (nodeChildren5_bounds i).2.trans_lt (by decide)
    | inr i => exact badSmall x hx i
  let σ := 1-bitSaving
  have sigma : 0 ≤ σ := by norm_num [σ,bitSaving]
  have hσ : σ ≤ 1 := by norm_num [σ,bitSaving]
  have good : (∑ i : Fin nodeChildren5.length, (1/(142080 : ℝ))*((nodeChildren5[i.val] : ℝ)/64)^σ) ≤ 1-1/2^24 := by
    rw [occurrence_moment_eq nodeChildren5_realizes,histMoment_five]
    have cert := bit_histMoment_le
    dsimp only [σ]
    linarith
  have weights (x i) : 0 ≤ weight x i := by cases i with
    | inl i => norm_num [weight]
    | inr i => exact nonneg x i
  let arity := fun x => Fintype.card (Fin nodeChildren5.length ⊕ Fin (bad x))
  let e := fun x => (Fintype.equivFin (Fin nodeChildren5.length ⊕ Fin (bad x))).symm
  have moment (x) (hx : u ≤ atoms x) :
      (∑ i, weight x i*((rank x i : ℝ)/64)^σ) ≤ 1-1/2^25 := by
    rw [Fintype.sum_sum_type]
    exact (add_le_add good (fallback x hx)).trans (by norm_num)
  have linear (x) (hx : u ≤ atoms x) :
      (∑ i, weight x i*((rank x i : ℝ)/64)) ≤ 1-1/2^25 := by
    apply le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left _ (weights x i)) (moment x hx)
    intro i _
    by_cases zero : rank x i = 0
    · simp only [zero,Nat.cast_zero,zero_div]; exact Real.rpow_nonneg (by norm_num) _
    have hp : 0 < rank x i := Nat.pos_of_ne_zero zero
    conv_lhs => rw [← Real.rpow_one ((rank x i : ℝ)/64)]
    apply Real.rpow_le_rpow_of_exponent_ge (by positivity) _ hσ
    have := small x hx i
    exact (div_le_one (by norm_num)).2 (by exact_mod_cast this.le)
  have closed := M8.StoppedRecurrence.stopped_closed atoms arity (fun x i => next x (e x i))
    (fun x i => rank x (e x i)) (fun x i => weight x (e x i)) cost u (m := 64) (τ := σ)
    (q₁ := 1-1/2^25) (qτ := 1-1/2^25) (by norm_num) sigma hc hl (by norm_num) (by norm_num)
    (by norm_num) (fun x i => weights x _) pos leaf (by
      intro x hx i
      have lt : ((rank x (e x i) : ℝ)/64) < 1 := (div_lt_one (by norm_num)).2 (by exact_mod_cast small x hx (e x i))
      have bound := (scale x hx (e x i)).trans_lt (mul_lt_mul_of_pos_right lt (by exact_mod_cast pos x))
      rw [one_mul] at bound
      exact_mod_cast bound) (fun x hx i => scale x hx _) (by
      intro x hx
      rw [Equiv.sum_comp (e x) (fun i => weight x i*cost (next x i))]
      exact node x hx)
    (by intro x hx; rw [Equiv.sum_comp (e x) (fun i => weight x i*((rank x i : ℝ)/64))]; exact linear x hx)
    (by intro x hx; rw [Equiv.sum_comp (e x) (fun i => weight x i*((rank x i : ℝ)/64)^σ)]; exact moment x hx)
  intro x
  convert closed x using 1
  dsimp only [σ]
  ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
