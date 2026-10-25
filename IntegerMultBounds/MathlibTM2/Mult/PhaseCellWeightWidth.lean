module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBody

/-! A logarithmic geometry allowance bounds all similarity setup arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def weightWorkspaceWidth (P q w t u : ℕ) : ℕ :=
  coefficientWorkspaceWidth P (w + q + 2) t u 0 t

/-- One width covers every ambient coordinate and all setup parameters. -/
theorem weightWorkspaceWidth_facts {P q w s t u lo L : ℕ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : lo < s) (hL : L ≤ s) :
    let V := weightWorkspaceWidth P q w t u
    w ≤ V ∧ 13 * P + 8 ≤ V ∧ q + P + 2 ≤ V ∧
      lo + L < 2 ^ V ∧ L < 2 ^ V ∧ 2 * s < 2 ^ V ∧ t < 2 ^ V ∧
      s ^ 2 < 2 ^ V ∧ u * s ^ 2 < 2 ^ V ∧ similarityDenominator s t < 2 ^ V ∧
      ∀ j < s, 2 * t * j + s < 2 ^ V ∧
        similarityNumerator s t u j * 2 ^ (5 * P + 2) < 2 ^ V := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨_, _, _, htV, _, _, _, hbig⟩ :=
    coefficientWorkspaceWidth_bound P (w + q + 2) s t u 0 t hst.le
  change u * t * (t + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V at hbig
  have ht : 1 ≤ t := by omega
  have hbase : t ^ 2 ≤ u * t * (t + 1) ^ 2 := by
    have hsq : t ≤ (t + 1) ^ 2 := by nlinarith
    have hut : t ≤ u * t := by nlinarith
    simpa only [pow_two] using Nat.mul_le_mul hut hsq
  have hp8 : 8 ≤ 2 ^ (13 * P + 8) := by
    exact (show 8 = 2 ^ 3 by decide).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hsmall : 8 * t ^ 2 < 2 ^ V :=
    (show 8 * t ^ 2 ≤ u * t * (t + 1) ^ 2 * 2 ^ (13 * P + 8) by
      nlinarith only [hbase, hp8]).trans_lt hbig
  have hs2 : s ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hnum : u * s ^ 2 ≤ u * t * (t + 1) ^ 2 := by
    have hmul := Nat.mul_le_mul_left u hs2
    have hmulT : u * (t + 1) ^ 2 ≤ u * t * (t + 1) ^ 2 := by nlinarith
    exact hmul.trans hmulT
  have hone : 1 ≤ 2 ^ (13 * P + 8) := Nat.one_le_two_pow
  have huV : u * s ^ 2 < 2 ^ V :=
    (hnum.trans (by simpa using Nat.mul_le_mul_left (u * t * (t + 1) ^ 2) hone)).trans_lt hbig
  refine ⟨by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth]; omega,
    by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth]; omega,
    by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth]; omega,
    ?_, ?_, ?_, htV, ?_, huV, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · unfold similarityDenominator
    have hsub : t - s ≤ t := Nat.sub_le _ _
    nlinarith
  · intro j hj
    constructor
    · nlinarith
    · have ha := similarityNumerator_le s t u j
      have hpow : 2 ^ (5 * P + 2) ≤ 2 ^ (13 * P + 8) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact (Nat.mul_le_mul (ha.trans hnum) hpow).trans_lt hbig

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
