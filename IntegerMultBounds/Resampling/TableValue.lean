import IntegerMultBounds.Resampling.TabDTape
import IntegerMultBounds.Resampling.B0Value
import IntegerMultBounds.Resampling.TabledMaps

/-! The words written by the table machines, read back: every word has width
`w`, the A and E words have signed value the table entry (zero at the
off-diagonal centre), the D and halving words have signed value the negated
entry, and every signed value is at most `2^p` in magnitude. These are the
hypotheses of `accumulators_eq_W` and `b0_value_W` for the tables
`tableA`, `tableE`, `tableD` of `tables_ok`. -/

namespace IntegerMultBounds.Resampling.TableValue

open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.Registers (canon)
open IntegerMultBounds.Machine.RegWord (padTo padTo_length signed_padTo canon_length_lt)
open IntegerMultBounds.Machine.TwosComplement (signed)
open IntegerMultBounds.Machine.GaussianLine (centre)
open IntegerMultBounds.Resampling.TabATape (wA tabA)
open IntegerMultBounds.Resampling.TabETape (uu cc bb An Ap Xn wE tabF bb_le uu_lt cc_cases wE_neg wE_pos wE_zero)
open IntegerMultBounds.Resampling.TabDTape (negv dW hW signed_negv canon_negv)
open Real

section ExpBounds

theorem expNeg_le_succ (p a b : ℕ) (hp : 13 ≤ p) (hb : 0 < b) : WeightNat.expPiNat true p a b ≤ 2 ^ p + 1 := by
  have h := WeightTable.expPi_neg_err p a b hp hb
  rw [WeightNat.expPi_eq_nat _ _ _ _ hp] at h
  have he : exp (-(π * a / b)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have h1 : ((WeightNat.expPiNat true p a b : ℤ) : ℝ) ≤ 2 ^ p + 3 / 2 := by
    have := (abs_le.mp h).2; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) p]
  have h2 : ((WeightNat.expPiNat true p a b : ℕ) : ℝ) < ((2 ^ p + 2 : ℕ) : ℝ) := by
    push_cast at h1 ⊢; linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)

theorem expNeg_le (p a b : ℕ) (hp : 13 ≤ p) (hb : 0 < b) (hab : b ≤ a) : WeightNat.expPiNat true p a b ≤ 2 ^ p := by
  have h := WeightTable.expPi_neg_err p a b hp hb
  rw [WeightNat.expPi_eq_nat _ _ _ _ hp] at h
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hab' : (1 : ℝ) ≤ π * a / b := by
    rw [le_div_iff₀ hbr]
    have : (b : ℝ) ≤ a := by exact_mod_cast hab
    nlinarith [Real.pi_gt_three]
  have he1 : exp (-(π * a / b)) ≤ exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he2 : exp (-1 : ℝ) < 1 / 2 := by
    rw [Real.exp_neg]
    have : (2 : ℝ) < exp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have hp2 : (8 : ℝ) ≤ 2 ^ p := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h1 : ((WeightNat.expPiNat true p a b : ℤ) : ℝ) < 2 ^ p + 1 := by
    have := (abs_le.mp h).2; nlinarith
  have h2 : ((WeightNat.expPiNat true p a b : ℕ) : ℝ) < ((2 ^ p + 1 : ℕ) : ℝ) := by
    push_cast at h1 ⊢; linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)

end ExpBounds

section Words

theorem padTo_width (v w : ℕ) (hv : v < 2 ^ (w - 1)) (hw : 1 ≤ w) : (padTo v w).length = w :=
  padTo_length _ _ (canon_length_lt v w hw hv).le

theorem getD_tabF (f : ℕ → ℕ) (w N e : ℕ) (he : e < N) : (tabF f w N).getD e [] = padTo (f e) w := by
  unfold tabF
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  rfl

theorem mem_tabF (f : ℕ → ℕ) (w N : ℕ) (x : List Bool) (hx : x ∈ tabF f w N) : ∃ e < N, x = padTo (f e) w := by
  unfold tabF at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact ⟨e, List.mem_range.mp he, rfl⟩

theorem tabF_length (f : ℕ → ℕ) (w N : ℕ) : (tabF f w N).length = N := by simp [tabF]

end Words

section TableA

variable (s t m α p w : ℕ)

theorem wA_le (hp : 13 ≤ p) (hα : 2 ≤ α) (ht : 0 < t) (e : ℕ) : wA s t m α p e ≤ 2 ^ p := by
  unfold wA WeightNat.tableANat
  apply Nat.div_le_of_le_mul
  have := expNeg_le_succ p (((s : ℤ) * ((e / (2 * m + 1) : ℕ) : ZMod t).val -
    t * ((centre s t (e / (2 * m + 1)) : ℤ) - m + (e % (2 * m + 1) : ℕ))) ^ 2).toNat (α ^ 2 * t ^ 2) hp
    (Nat.mul_pos (pow_pos (by omega) 2) (pow_pos ht 2))
  have h2 : 2 ^ p + 1 ≤ 2 * 2 ^ p := by have := Nat.one_le_two_pow (n := p); omega
  calc _ ≤ 2 ^ p + 1 := this
    _ ≤ 2 * 2 ^ p := h2
    _ ≤ α * 2 ^ p := Nat.mul_le_mul_right _ hα

theorem div_mod_entry (n k j : ℕ) (hj : j < n) : (k * n + j) / n = k ∧ (k * n + j) % n = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem lt_entry (n N k j : ℕ) (hk : k < N) (hj : j < n) : k * n + j < N * n := by
  have : (k + 1) * n ≤ N * n := Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at this; omega

/-- The A-table words: width `w`, magnitude at most `2^p`, `t (2m+1)` of
them, and entry `k (2m+1) + j` has signed value `tableA k (⌊sk/t⌋ − m + j)`. -/
theorem tabA_ok (hp : 13 ≤ p) (hα : 2 ≤ α) (ht : 0 < t) (hw : p + 2 ≤ w) :
    (∀ e, e < t * (2 * m + 1) → (canon (wA s t m α p e)).length ≤ w) ∧
    (∀ x ∈ tabA s t m α p w (t * (2 * m + 1)), x.length = w) ∧
    (∀ x ∈ tabA s t m α p w (t * (2 * m + 1)), |signed x| ≤ 2 ^ p) ∧
    (tabA s t m α p w (t * (2 * m + 1))).length = t * (2 * m + 1) ∧
    ∀ k j, k < t → j < 2 * m + 1 →
      signed ((tabA s t m α p w (t * (2 * m + 1))).getD (k * (2 * m + 1) + j) []) =
        WeightTable.tableA s t α p (k : ZMod t) ((centre s t k : ℤ) - m + j) := by
  have hlt : ∀ e, wA s t m α p e < 2 ^ (w - 1) := fun e =>
    (wA_le s t m α p hp hα ht e).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have htab : tabA s t m α p w (t * (2 * m + 1)) = tabF (wA s t m α p) w (t * (2 * m + 1)) := rfl
  refine ⟨fun e _ => (canon_length_lt _ _ (by omega) (hlt e)).le, fun x hx => ?_, fun x hx => ?_,
    by rw [htab, tabF_length], fun k j hk hj => ?_⟩
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x (htab ▸ hx)
    exact padTo_width _ _ (hlt e) (by omega)
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x (htab ▸ hx)
    rw [signed_padTo _ _ (by omega) (hlt e), abs_of_nonneg (by positivity)]
    exact_mod_cast wA_le s t m α p hp hα ht e
  · obtain ⟨h1, h2⟩ := div_mod_entry (2 * m + 1) k j hj
    rw [htab, getD_tabF _ _ _ _ (lt_entry _ _ _ _ hk hj), signed_padTo _ _ (by omega) (hlt _),
      WeightNat.tableA_nat _ _ _ _ hp]
    unfold wA
    rw [h1, h2]

end TableA

section TableE

variable (s t α p n w : ℕ)

/-- The exponent numerator is at least the denominator when `s ≤ α²(t − s)`. -/
theorem big (hs : 0 < s) (hst : s ≤ t) (hθ : s ≤ α ^ 2 * (t - s)) (A x : ℕ) (hA : 2 * t ≤ 2 * A + s) :
    s ^ 2 ≤ α ^ 2 * (A ^ 2 - bb s t x ^ 2) := by
  have hb := bb_le s t hs x
  have hbA : bb s t x ≤ A := by omega
  generalize bb s t x = B at hb hbA ⊢
  obtain ⟨T, rfl⟩ : ∃ T, t = s + T := ⟨t - s, by omega⟩
  rw [show s + T - s = T by omega] at hθ
  zify [Nat.pow_le_pow_left hbA 2] at hθ hA hb ⊢
  have e1 : (s : ℤ) ^ 2 + 4 * s * T ≤ 4 * (A : ℤ) ^ 2 := by nlinarith
  have e2 : 4 * (B : ℤ) ^ 2 ≤ (s : ℤ) ^ 2 := by nlinarith [B.cast_nonneg (α := ℤ)]
  have e3 : (s : ℤ) * T ≤ (A : ℤ) ^ 2 - (B : ℤ) ^ 2 := by linarith
  have e4 : (s : ℤ) * s ≤ s * ((α : ℤ) ^ 2 * T) := mul_le_mul_of_nonneg_left hθ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℤ) ≤ (α : ℤ) ^ 2)]

theorem an_big (hs : 0 < s) (hst : s ≤ t) (ℓ d : ℕ) (hd : 1 ≤ d) : 2 * t ≤ 2 * An s t ℓ d + s := by
  have hT : t ≤ t * d := Nat.le_mul_of_pos_right t hd
  have := uu_lt s t hs ℓ
  unfold An
  rcases cc_cases s t hs ℓ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;>
    generalize t * d = T at hT ⊢ <;> omega

theorem ap_big (hs : 0 < s) (hst : s ≤ t) (ℓ d : ℕ) (hd : 1 ≤ d) : 2 * t ≤ 2 * Ap s t ℓ d + s := by
  have hT : t ≤ t * d := Nat.le_mul_of_pos_right t hd
  have := uu_lt s t hs ℓ
  unfold Ap
  rcases cc_cases s t hs ℓ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;>
    generalize t * d = T at hT ⊢ <;> omega

theorem wE_le (hp : 13 ≤ p) (hs : 0 < s) (hst : s ≤ t) (hθ : s ≤ α ^ 2 * (t - s)) (e : ℕ)
    (he : e < s * (2 * n + 1)) : wE s t α p n e ≤ 2 ^ p := by
  rcases lt_trichotomy (e % (2 * n + 1)) n with hj | hj | hj
  · rw [← wE_neg s t α p n e hs hst he hj]
    exact expNeg_le _ _ _ hp (pow_pos hs 2) (big s t α hs hst hθ _ _ (an_big s t hs hst _ _ (by omega)))
  · rw [wE_zero s t α p n e hj]; positivity
  · rw [← wE_pos s t α p n e hs hst he hj]
    exact expNeg_le _ _ _ hp (pow_pos hs 2) (big s t α hs hst hθ _ _ (ap_big s t hs hst _ _ (by omega)))

/-- The E-table words: width `w`, magnitude at most `2^p`, `s (2n+1)` of
them, and entry `k (2n+1) + j` has signed value `tableE k (j − n)`, zero at
`j = n`. -/
theorem tabE_ok (hp : 13 ≤ p) (hs : 0 < s) (hst : s ≤ t) (hθ : s ≤ α ^ 2 * (t - s)) (hw : p + 2 ≤ w) :
    (∀ e, e < s * (2 * n + 1) → (canon (wE s t α p n e)).length ≤ w) ∧
    (∀ x ∈ tabF (wE s t α p n) w (s * (2 * n + 1)), x.length = w) ∧
    (∀ x ∈ tabF (wE s t α p n) w (s * (2 * n + 1)), |signed x| ≤ 2 ^ p) ∧
    (tabF (wE s t α p n) w (s * (2 * n + 1))).length = s * (2 * n + 1) ∧
    ∀ k j, k < s → j < 2 * n + 1 →
      signed ((tabF (wE s t α p n) w (s * (2 * n + 1))).getD (k * (2 * n + 1) + j) []) =
        if -(n : ℤ) + j = 0 then 0 else WeightTable.tableE s t α p (k : ZMod s) (-(n : ℤ) + j) := by
  have hlt : ∀ e, e < s * (2 * n + 1) → wE s t α p n e < 2 ^ (w - 1) := fun e he =>
    (wE_le s t α p n hp hs hst hθ e he).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  refine ⟨fun e he => (canon_length_lt _ _ (by omega) (hlt e he)).le, fun x hx => ?_, fun x hx => ?_,
    tabF_length _ _ _, fun k j hk hj => ?_⟩
  · obtain ⟨e, he, rfl⟩ := mem_tabF _ _ _ x hx
    exact padTo_width _ _ (hlt e he) (by omega)
  · obtain ⟨e, he, rfl⟩ := mem_tabF _ _ _ x hx
    rw [signed_padTo _ _ (by omega) (hlt e he), abs_of_nonneg (by positivity)]
    exact_mod_cast wE_le s t α p n hp hs hst hθ e he
  · obtain ⟨h1, h2⟩ := div_mod_entry (2 * n + 1) k j hj
    have hkj := lt_entry _ _ _ _ hk hj
    rw [getD_tabF _ _ _ _ hkj, signed_padTo _ _ (by omega) (hlt _ hkj)]
    unfold wE
    rw [h1, h2]
    by_cases hjn : j = n
    · subst hjn; simp
    · have : ¬ (-(n : ℤ) + j = 0) := by omega
      simp only [hjn, this, ↓reduceIte]
      rw [WeightNat.tableE_nat _ _ _ _ hp]

end TableE

section TableD

variable (s t α p w : ℕ) [NeZero s] [NeZero t]

theorem tableDNat_le (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) (ℓ : ZMod s) :
    WeightNat.tableDNat s t α p ℓ ≤ 2 ^ p := by
  have := (WeightTable.tableD_spec s t α p hp hα hαp ℓ).2.2
  rw [WeightNat.tableD_nat _ _ _ _ hp] at this
  exact_mod_cast this

/-- The D-table and halving words: width `w`, magnitude at most `2^p`, `s`
of each; the D word `ℓ` has signed value `−tableD ℓ` and every halving word
`−2^(p−1)`. -/
theorem tabD_ok (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) (hw : p + 2 ≤ w) :
    (∀ ℓ < s, WeightNat.tableDNat s t α p (ℓ : ZMod s) ≤ 2 ^ w) ∧
    (∀ x ∈ tabF (dW s t α p w) w s, x.length = w) ∧
    (∀ x ∈ tabF (dW s t α p w) w s, |signed x| ≤ 2 ^ p) ∧
    (tabF (dW s t α p w) w s).length = s ∧
    (∀ k < s, signed ((tabF (dW s t α p w) w s).getD k []) = -WeightTable.tableD s t α p (k : ZMod s)) ∧
    (∀ x ∈ tabF (hW w p) w s, x.length = w) ∧
    (∀ x ∈ tabF (hW w p) w s, signed x = -2 ^ (p - 1)) ∧
    (tabF (hW w p) w s).length = s := by
  have hpw : 2 ^ p ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right two_pos (by omega)
  have hD : ∀ ℓ : ℕ, WeightNat.tableDNat s t α p (ℓ : ZMod s) ≤ 2 ^ (w - 1) := fun ℓ =>
    (tableDNat_le s t α p hp hα hαp _).trans hpw
  have hH : 2 ^ (p - 1) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right two_pos (by omega)
  refine ⟨fun ℓ _ => (hD ℓ).trans (Nat.pow_le_pow_right two_pos (by omega)), fun x hx => ?_, fun x hx => ?_,
    tabF_length _ _ _, fun k hk => ?_, fun x hx => ?_, fun x hx => ?_, tabF_length _ _ _⟩
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x hx
    exact padTo_length _ _ (canon_negv _ _)
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x hx
    rw [dW, signed_negv _ _ (by omega) (hD e), abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast tableDNat_le s t α p hp hα hαp _
  · rw [getD_tabF _ _ _ _ hk, dW, signed_negv _ _ (by omega) (hD k), WeightNat.tableD_nat _ _ _ _ hp]
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x hx
    exact padTo_length _ _ (canon_negv _ _)
  · obtain ⟨e, -, rfl⟩ := mem_tabF _ _ _ x hx
    rw [hW, signed_negv _ _ (by omega) hH]
    push_cast; rfl

end TableD

section Assembly

open IntegerMultBounds.Resampling.NeumannWords (vec iter)
open IntegerMultBounds.Resampling.B0Words (vsel oneStep)
open IntegerMultBounds.NLogN (sqrtWindow)

theorem theta_nat (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) :
    s ≤ α ^ 2 * (t - s) := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have h : (s : ℝ) ≤ (α : ℝ) ^ 2 * ((t : ℝ) - s) := by
    have := mul_le_mul_of_nonneg_left hθ hsr.le
    rw [mul_one] at this
    calc (s : ℝ) ≤ s * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) := this
      _ = (α : ℝ) ^ 2 * ((t : ℝ) - s) := by field_simp
  have : ((α ^ 2 * (t - s) : ℕ) : ℝ) = (α : ℝ) ^ 2 * ((t : ℝ) - s) := by push_cast [Nat.cast_sub hst.le]; ring
  exact_mod_cast this ▸ h

/-- The `B̃₀` machine fed with the words of the table machines computes the
numerators of `B̃₀` with the tables `tableE`, `tableD` of `tables_ok`. -/
theorem b0_tables (s t α p w W : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) (hp : 13 ≤ p) (hw : p + 3 ≤ w) (hwW : w ≤ W)
    (hWW : ((2 * sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (win zeros : List (List Bool))
    (hwin : win.length = 2 * t) (hwinw : ∀ x ∈ win, x.length = w) (hwinb : ∀ x ∈ win, |signed x| ≤ 2 ^ p)
    (hwv : ‖vec t p win‖ ≤ 1)
    (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s) :
    vec s p (oneStep (tabF (dW s t α p w) w s) zeros s p w
        (iter (tabF (wE s t α p (sqrtWindow p)) w (s * (2 * sqrtWindow p + 1)))
          (oneStep (tabF (hW w p) w s) zeros s p w (vsel win s t)) s (sqrtWindow p) p w W p)) =
      TabledMaps.resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WeightTable.tableE s t α p ℓ h : ℝ) / 2 ^ p)
        (fun ℓ => (WeightTable.tableD s t α p ℓ : ℝ) / 2 ^ p) (vec t p win) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hok := WeightTable.tables_ok s t α p hst hp hα hαp
  obtain ⟨-, hEw, hEb, hEl, hEs⟩ := tabE_ok s t α p (sqrtWindow p) w hp hs hst.le (theta_nat s t α hs hst hθ) (by omega)
  obtain ⟨-, hDw, hDb, hDl, hDs, hHw, hHs, hHl⟩ := tabD_ok s t α p w hp (by omega) hαp (by omega)
  exact B0Value.b0_value_W hst (by positivity) hθ hp hw hwW hWW (WeightTable.tableE s t α p)
    (WeightTable.tableD s t α p) hok.2.1 win _ _ _ zeros hwin hwinw hwinb hwv hHw (by rw [hHl]; ring) hHs
    (fun k j hk hj => hEs k j hk hj) hEw hEb hEl hDw (by rw [hDl]; ring) hDb hDs hz hzl

/-- The Gaussian line machine fed with the A-table words computes the
window sums of `Ã` with the table `tableA` of `tables_ok`. -/
theorem a_tables (s t m α p w W : ℕ) [NeZero s] [NeZero t] (hα : 2 ≤ α) (hp : 13 ≤ p)
    (uWords : List (List Bool)) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
    (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)
    (hre : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q) []) = ar ((q : ℤ) - m))
    (him : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q + 1) []) = ai ((q : ℤ) - m))
    (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hul' : ∀ x ∈ uWords, x.length = w) (hub : ∀ x ∈ uWords, |signed x| ≤ 2 ^ p)
    (hul : 2 * (s + 2 * m + 1) ≤ uWords.length) (hst : s ≤ t) (k : ℕ) (hk : k < t) :
    NLogN.resampANum s t m (WindowSum.termW p fun k j => (WeightTable.tableA s t α p k j : ℝ) / 2 ^ p) u (k : ZMod t) =
      ⟨(signed (GaussianLine.accR (tabA s t m α p w (t * (2 * m + 1))) uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1),
       (signed (GaussianLine.accI (tabA s t m α p w (t * (2 * m + 1))) uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1)⟩ := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨-, hAw, hAb, hAl, hAs⟩ := tabA_ok s t m α p w hp hα ht hw
  exact TabledMaps.accumulators_eq_W _ uWords s t m p w W (WeightTable.tableA s t α p) u ar ai hu hAs hre him
    hw hwW hW hAw hul' hAb hub hAl hul hst hs k hk

end Assembly

end IntegerMultBounds.Resampling.TableValue
