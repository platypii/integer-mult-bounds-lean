import IntegerMultBounds.NLogN.SynthConv
import IntegerMultBounds.NLogN.Bluestein

/-! The embedding of complex cyclic convolutions into the synthetic ring,
Section 3.2 of Harvey and van der Hoeven. Twisting a length-`r` vector by
`ζ^k` with `ζ = e^(πi/r)` turns the cyclic convolution on `Fin r` into the
negacyclic product of `FixedOps.lean`, because the sign picked up on an
index wrap is exactly `ζ^r = -1`. Applied to the last coordinate, a cyclic
convolution on `G × Fin r` for any finite abelian group `G` becomes the
`G`-indexed cyclic convolution with coefficients in the synthetic ring; the
twist and its inverse are isometries of the sup norm. Fixed-point errors of
the twist and the bit cost of computing `ζ^k` are not treated here. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Twist

variable {r : ℕ} [NeZero r]

/-- The twist root `ζ^k` with `ζ = e^(πi/r)`. -/
noncomputable def twistRoot (r : ℕ) (k : ℕ) : ℂ := Complex.exp (π * I * k / r)

omit [NeZero r] in
theorem norm_twistRoot (k : ℕ) : ‖twistRoot r k‖ = 1 := by
  unfold twistRoot
  have : (π : ℂ) * I * k / r = ((π * k / r : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

omit [NeZero r] in
theorem twistRoot_mul (a b : ℕ) : twistRoot r a * twistRoot r b = twistRoot r (a + b) := by
  unfold twistRoot
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem twistRoot_add_r (k : ℕ) : twistRoot r (k + r) = -twistRoot r k := by
  rw [← twistRoot_mul]
  unfold twistRoot
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have : (π : ℂ) * I * r / r = π * I := by field_simp
  rw [this, Complex.exp_pi_mul_I]
  ring

omit [NeZero r] in
theorem conj_twistRoot_mul (k : ℕ) : (starRingEnd ℂ) (twistRoot r k) * twistRoot r k = 1 := by
  rw [Complex.conj_mul', norm_twistRoot]
  norm_num

/-- The sign of the index wrap is the twist root at `r`. -/
theorem twistRoot_sub (k i : Fin r) :
    twistRoot r i.val * twistRoot r (k - i).val = negaSign k i * twistRoot r k.val := by
  unfold negaSign
  split_ifs with h
  · have hv := Fin.coe_sub_iff_le.mpr h
    have hle : i.val ≤ k.val := Fin.le_iff_val_le_val.mp h
    rw [twistRoot_mul, show i.val + (k - i).val = k.val by omega]
    ring
  · have hlt : k < i := not_le.mp h
    have hv := Fin.coe_sub_iff_lt.mpr hlt
    have hlt' : k.val < i.val := Fin.lt_def.mp hlt
    rw [twistRoot_mul, show i.val + (k - i).val = k.val + r by omega, twistRoot_add_r]
    ring

omit [NeZero r] in
theorem negaSign_mul_self (k i : Fin r) : negaSign k i * negaSign k i = 1 := by
  unfold negaSign
  split_ifs <;> norm_num

/-- The paper's map `S`: multiply coordinate `k` by `ζ^k`. -/
noncomputable def twist (r : ℕ) (a : Fin r → ℂ) : Fin r → ℂ :=
  fun k => twistRoot r k.val * a k

/-- The inverse twist. -/
noncomputable def untwist (r : ℕ) (a : Fin r → ℂ) : Fin r → ℂ :=
  fun k => (starRingEnd ℂ) (twistRoot r k.val) * a k

omit [NeZero r] in
theorem untwist_twist (a : Fin r → ℂ) : untwist r (twist r a) = a := by
  funext k
  unfold untwist twist
  rw [← mul_assoc, conj_twistRoot_mul, one_mul]

omit [NeZero r] in
theorem twist_untwist (a : Fin r → ℂ) : twist r (untwist r a) = a := by
  funext k
  unfold untwist twist
  rw [← mul_assoc, mul_comm (twistRoot r k.val), conj_twistRoot_mul, one_mul]

omit [NeZero r] in
theorem norm_twist_apply (a : Fin r → ℂ) (k : Fin r) : ‖twist r a k‖ = ‖a k‖ := by
  unfold twist
  rw [norm_mul, norm_twistRoot, one_mul]

omit [NeZero r] in
theorem norm_twist (a : Fin r → ℂ) : ‖twist r a‖ = ‖a‖ := by
  simp only [Pi.norm_def]
  congr 1
  exact Finset.sup_congr rfl fun k _ => Subtype.ext (norm_twist_apply a k)

omit [NeZero r] in
theorem norm_untwist_apply (a : Fin r → ℂ) (k : Fin r) : ‖untwist r a k‖ = ‖a k‖ := by
  unfold untwist
  rw [norm_mul, Complex.norm_conj, norm_twistRoot, one_mul]

omit [NeZero r] in
theorem norm_untwist (a : Fin r → ℂ) : ‖untwist r a‖ = ‖a‖ := by
  simp only [Pi.norm_def]
  congr 1
  exact Finset.sup_congr rfl fun k _ => Subtype.ext (norm_untwist_apply a k)

omit [NeZero r] in
theorem norm_twist_le (a : Fin r → ℂ) : ‖twist r a‖ ≤ ‖a‖ := (norm_twist a).le

omit [NeZero r] in
theorem twist_sum {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    twist r (∑ i ∈ s, f i) = ∑ i ∈ s, twist r (f i) := by
  funext k
  simp only [twist, Finset.sum_apply, Finset.mul_sum]

/-- The one-coordinate identity: cyclic convolution becomes negacyclic after
twisting. -/
theorem negacyclicMul_twist (a b : Fin r → ℂ) :
    negacyclicMul (twist r a) (twist r b) = twist r (convG a b) := by
  funext k
  unfold negacyclicMul convG negaIdx
  simp only [twist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := twistRoot_sub k i
  calc negaSign k i * (twistRoot r i.val * a i) * (twistRoot r (k - i).val * b (k - i))
      = negaSign k i * (twistRoot r i.val * twistRoot r (k - i).val) * (a i * b (k - i)) := by
        ring
    _ = (negaSign k i * negaSign k i) * twistRoot r k.val * (a i * b (k - i)) := by
        rw [h]; ring
    _ = _ := by rw [negaSign_mul_self]; ring

end Twist

section Transport

variable {r : ℕ} [NeZero r] {G : Type*} [AddCommGroup G] [Fintype G]

/-- The cyclic convolution over `G` with coefficients in the synthetic ring. -/
noncomputable def synthConvG (U V : G → (Fin r → ℂ)) : G → (Fin r → ℂ) :=
  fun k => ∑ i, negacyclicMul (U i) (V (k - i))

omit [NeZero r] in
theorem synthConvG_eq_synthConv {t : ℕ} [NeZero t] (u v : Fin t → (Fin r → ℂ)) :
    synthConvG u v = synthConv t u v := rfl

/-- The paper's map `T`: twist the last coordinate of every slice. -/
noncomputable def toSynth (u : G × Fin r → ℂ) : G → (Fin r → ℂ) :=
  fun j => twist r (fun k => u (j, k))

/-- The paper's map `U = T⁻¹`. -/
noncomputable def ofSynth (w : G → (Fin r → ℂ)) : G × Fin r → ℂ :=
  fun p => untwist r (w p.1) p.2

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem ofSynth_toSynth (u : G × Fin r → ℂ) : ofSynth (toSynth u) = u := by
  funext p
  unfold ofSynth toSynth
  rw [untwist_twist]

omit [NeZero r] [AddCommGroup G] [Fintype G] in
theorem toSynth_ofSynth (w : G → (Fin r → ℂ)) : toSynth (ofSynth w) = w := by
  funext j
  unfold ofSynth toSynth
  exact twist_untwist (w j)

omit [NeZero r] [AddCommGroup G] in
theorem norm_toSynth_le (u : G × Fin r → ℂ) (j : G) : ‖toSynth u j‖ ≤ ‖u‖ := by
  unfold toSynth
  rw [norm_twist, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  exact norm_le_pi_norm u (j, k)

omit [NeZero r] [AddCommGroup G] in
theorem norm_ofSynth_le (w : G → (Fin r → ℂ)) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ j, ‖w j‖ ≤ M) :
    ‖ofSynth w‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro p
  unfold ofSynth
  rw [norm_untwist_apply]
  exact (norm_le_pi_norm (w p.1) p.2).trans (hw p.1)

/-- The transport of convolutions: `M_ℂ(u, v) = U(M_R(T u, T v))` in the paper's
notation, here as `T (u ∗ v) = (T u) ∗_R (T v)`. -/
theorem synthConvG_toSynth (u v : G × Fin r → ℂ) :
    synthConvG (toSynth u) (toSynth v) = toSynth (convG u v) := by
  funext j
  unfold synthConvG
  simp only [toSynth, negacyclicMul_twist]
  rw [← twist_sum]
  congr 1
  funext k
  simp only [Finset.sum_apply, convG, Fintype.sum_prod_type, Prod.mk_sub_mk]

theorem convG_eq_ofSynth (u v : G × Fin r → ℂ) :
    convG u v = ofSynth (synthConvG (toSynth u) (toSynth v)) := by
  rw [synthConvG_toSynth, ofSynth_toSynth]

/-- The two-coordinate case on `Fin t × Fin r`. -/
theorem synthConv_toSynth {t : ℕ} [NeZero t] (u v : Fin t × Fin r → ℂ) :
    synthConv t (toSynth u) (toSynth v) = toSynth (convG u v) :=
  synthConvG_toSynth u v

end Transport

end IntegerMultBounds.NLogN
