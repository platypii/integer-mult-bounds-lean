module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreRouteCharge
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.NLogN.PhaseCellCoreQuotient

/-! Every fixed polynomial core width satisfies the key-width comparison on
selected axes. The quotient gate follows from actual axis density and growth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedAxis_le_four_ambient {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    2^Sizes.ℓ n ≤ 4*Sizes.s n i := by
  have hlower := (h.good.bounds i).lower
  have hd := h.one_le_d
  have ht : Sizes.t n i ≤ 2*Sizes.s n i := by
    by_contra hc
    have hc' : 2*Sizes.s n i ≤ Sizes.t n i := by omega
    have hm := Nat.mul_le_mul_left (Sizes.d n) hc'
    have hu : Sizes.t n i ≤ Sizes.d n*Sizes.t n i := Nat.le_mul_of_pos_left _ hd
    nlinarith only [hlower,hm,hu]
  have hr : 2^Sizes.ℓ n ≤ 2*Sizes.t n i := by
    have hell := h.two_le_ℓ
    have he : 2^Sizes.ℓ n = 2*2^(Sizes.ℓ n-1) := by
      rw [←pow_succ']
      congr 1
      omega
    unfold Sizes.t
    split_ifs <;> omega
  omega

/-- A power-of-two replica count drawn from the selected tensor has an exponent
no larger than the padded tensor's total coordinate width. -/
theorem selectedReplicaExponent_le {n : ℕ} (h : Sizes.Big n) (a : ℕ)
    (hvolume : 2^a ≤ Sizes.T n) : a ≤ Sizes.d n*Sizes.ℓ n := by
  have hlog : a ≤ Sizes.logT n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [Sizes.T] using hvolume
  exact hlog.trans (Sizes.logT_le_dℓ h.one_le_d)

theorem selectedPolynomialCoreWidth_quotient (C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (width : ℕ),
    0 < width → width ≤ C*(Sizes.p n)^e →
      2^((Sizes.ℓ n+1)/2)+2 ≤ Sizes.s n i/width := by
  filter_upwards [selectedAxis_eventually_polynomial (128*C^2) (2*e)] with n hpoly
  intro h i width hw hwidth
  have ht : Sizes.t n i ≤ 2^Sizes.ℓ n := by
    unfold Sizes.t
    split_ifs
    · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    · rfl
  have hp := (hpoly i).trans ht
  have hsquare := Nat.pow_le_pow_left hwidth 2
  have he : ((Sizes.p n)^e)^2 = (Sizes.p n)^(2*e) := by rw [←pow_mul,Nat.mul_comm e 2]
  rw [mul_pow,he] at hsquare
  have hsmall : 128*width^2 ≤ 2^Sizes.ℓ n := by nlinarith only [hp,hsquare]
  exact coreQuotient_large_of_square_width _ _ _ hw h.two_le_ℓ (selectedAxis_le_four_ambient h i) hsmall

theorem selectedPolynomialCoreRouteCharge_le (C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (a width radius L : ℕ),
    a ≤ Sizes.d n*Sizes.ℓ n → 0 < width → width ≤ C*(Sizes.p n)^e → radius ≤ width →
    L ∈ coreGatherLengths (Sizes.s n i) width radius →
    dyadicRouteCharge a (Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length) ≤
      18*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) := by
  filter_upwards [selectedPolynomialCoreWidth_quotient C e] with n hquot
  intro h i a width radius L ha hw hwidth hr hL
  exact selectedCoreGroupRouteCharge_le h i a width radius L ha hw hr (hquot h i width hw hwidth) hL

end IntegerMultBounds.MathlibTM2.Cost
