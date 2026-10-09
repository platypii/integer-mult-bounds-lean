import IntegerMultBounds.Machine.BinaryInterchangeRun

/-! Uniform certified time bound for the concrete width-selecting binary
interchange, including both physical comparisons and the selected branch. -/
namespace IntegerMultBounds.Machine.BinaryInterchangeRun
noncomputable section

private theorem short_canonical_budget (hs : Fin 5 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 5) :
    ∀ i, GrowingCounterData.Canonical (shortWords hs j i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc j

private theorem short_values_h (P G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i) :
    ∀ i, Counter.value (shortWords hs 3 i) = BinaryAdjacentWidthHeadersShared.values P G B h i := by
  intro i; fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
private theorem short_values_d (P G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i) :
    ∀ i, Counter.value (shortWords hs 4 i) = BinaryAdjacentWidthHeadersShared.values P G B d i := by
  intro i; fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 4

private theorem original_volume_bounds (P G B h d : ℕ)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    0 < BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B ∧
    h ≤ BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B ∧
    d ≤ BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B := by
  have hhp : 1 ≤ 2^h := Nat.one_le_pow _ _ (by omega)
  have hdp : 1 ≤ 2^d := Nat.one_le_pow _ _ (by omega)
  have hhb : 2^h ≤ P*2^h*G*2^d*B := by
    calc
      2^h = 1*2^h*1*1*1 := by ring
      _ ≤ P*2^h*G*2^d*B := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) (by omega)) hdp) (by omega)
  have hdb : 2^d ≤ P*2^h*G*2^d*B := by
    calc
      2^d = 1*1*1*2^d*1 := by ring
      _ ≤ P*2^h*G*2^d*B := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) hhp) (by omega)) le_rfl) (by omega)
  exact ⟨hhp.trans hhb,(Nat.le_of_lt (show h < 2^h from Nat.lt_two_pow_self)).trans hhb,
    (Nat.le_of_lt (show d < 2^d from Nat.lt_two_pow_self)).trans hdb⟩

private theorem width_factor_mono (u h d : ℕ) (hu : u ≤ max h d) :
    ((max 1 u : ℕ) : ℝ)^Parameters.tau ≤
      ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast max_le_max_left 1 hu
  · exact Shared50RecursiveBudgetBound.exponent_range.1.le

/-- The actual finite-control program's cost is uniformly bounded in the
original rectangular binary volume, for all adjacent widths including zero. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B h d : ℕ) (hs : Fin 5 → List Bool),
    0 < P → 0 < G → 0 < B → h ≤ d+1 → d ≤ h+1 →
    (∀ i, Counter.value (hs i) = values P G B h d i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B h d hs : ℝ) ≤
      C*(BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B : ℝ)*
        ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨E,hE,hEq⟩ := BinaryRadixEqualShared.uniform_bound
  obtain ⟨A,hA,hAdj⟩ := BinaryAdjacentWidthRun.uniform_bound
  refine ⟨E+A+44,by linarith,?_⟩
  intro P G B h d hs hP hG hB hhd hdh hv hc
  let V := BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B
  let F := ((max 1 (max h d) : ℕ) : ℝ)^Parameters.tau
  obtain ⟨hV,hhV,hdV⟩ := original_volume_bounds P G B h d hP hG hB
  have hsel := BinaryAdjacentWidthSelector.cost_volume (hs 3) (hs 4) (hc 3) (hc 4) V hV
    (by rw [hv]; exact hhV) (by rw [hv]; exact hdV)
  have hselR : (BinaryAdjacentWidthSelector.cost (hs 3) (hs 4)+1 : ℕ) ≤ 44*V := by omega
  have hselR' := (Nat.cast_le (α := ℝ)).mpr hselR
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hselR'
  have hF : 1 ≤ F := Real.one_le_rpow (by exact_mod_cast le_max_left 1 (max h d))
    Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlin := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg (α := ℝ) V)
  have hchosen : (BinaryAdjacentWidthSelectorDispatch.chosen h d
      (BinaryRadixEqualShared.cost P G B h (shortWords hs 3))
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4))
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) : ℝ) ≤ (E+A)*(V : ℝ)*F := by
    unfold BinaryAdjacentWidthSelectorDispatch.chosen
    split_ifs with hlt dlt
    · have hd : d = h+1 := by omega
      have hb := hAdj P G B h (shortWords hs 3) hP hG hB (short_values_h P G B h d hs hv)
        (short_canonical_budget hs hc 3)
      have he : BinaryAdjacentWidthHeadersShared.volume P G B h = V := by
        dsimp [V]; rw [hd,pow_succ]
        unfold BinaryAdjacentWidthHeadersShared.volume BinaryAdjacentWidthInterchange.volume
        ring
      rw [he] at hb
      have hm := width_factor_mono h h d (le_max_left _ _)
      have hmul := mul_le_mul_of_nonneg_left hm
        (mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) V))
      dsimp [F] at *
      have hepos := mul_nonneg (mul_nonneg hE.le (Nat.cast_nonneg (α := ℝ) V)) (by positivity : 0 ≤ F)
      nlinarith only [hb,hmul,hepos]
    · have hh : h = d+1 := by omega
      have hb := hAdj P G B d (shortWords hs 4) hP hG hB (short_values_d P G B h d hs hv)
        (short_canonical_budget hs hc 4)
      have he : BinaryAdjacentWidthHeadersShared.volume P G B d = V := by
        dsimp [V]; rw [hh,pow_succ]
        unfold BinaryAdjacentWidthHeadersShared.volume BinaryAdjacentWidthInterchange.volume
        ring
      rw [he] at hb
      have hm := width_factor_mono d h d (le_max_right _ _)
      have hmul := mul_le_mul_of_nonneg_left hm
        (mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) V))
      have hepos := mul_nonneg (mul_nonneg hE.le (Nat.cast_nonneg (α := ℝ) V)) (by positivity : 0 ≤ F)
      dsimp [F] at *
      nlinarith only [hb,hmul,hepos]
    · have heq : h = d := by omega
      have hb := hEq P G B h (shortWords hs 3) hP hG hB (short_values_h P G B h d hs hv)
        (short_canonical_budget hs hc 3)
      have he : RadixRangePadding.volume P (2^h) G B = V := by
        dsimp [V]; rw [← heq]
        unfold RadixRangePadding.volume BinaryAdjacentWidthInterchange.volume
        ring
      rw [he] at hb
      have hm := width_factor_mono h h d (le_max_left _ _)
      have hmul := mul_le_mul_of_nonneg_left hm
        (mul_nonneg hE.le (Nat.cast_nonneg (α := ℝ) V))
      have hapos := mul_nonneg (mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) V)) (by positivity : 0 ≤ F)
      dsimp [F] at *
      nlinarith only [hb,hmul,hapos]
  unfold cost
  simp only [Nat.cast_add,Nat.cast_one] at *
  have hcast : ((BinaryAdjacentWidthSelectorDispatch.chosen h d
      (BinaryRadixEqualShared.cost P G B h (shortWords hs 3))
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4))
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) : ℕ) : ℝ) =
      BinaryAdjacentWidthSelectorDispatch.chosen h d
      (BinaryRadixEqualShared.cost P G B h (shortWords hs 3) : ℝ)
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4) : ℝ)
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3) : ℝ) := by
    unfold BinaryAdjacentWidthSelectorDispatch.chosen
    split_ifs <;> rfl
  rw [hcast]
  change _ ≤ (E+A+44)*(V : ℝ)*F
  nlinarith only [hchosen,hselR',hlin]

end
end IntegerMultBounds.Machine.BinaryInterchangeRun
