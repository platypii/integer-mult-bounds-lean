module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFormattedClassSetupCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! The three shared format exports are scalar setup, paid once per class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem selectedClassSetupBounds_le (cD : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (D : ℕ),
      D ≤ cD*Sizes.p n →
      classSetupTimeBound D ≤ Sizes.T n ∧ classSetupStockBound D ≤ Sizes.T n ∧
        classSetupRetireBound D ≤ Sizes.T n := by
  let Ktime := 160*(cD+4)^2+174*cD+186
  let Kstock := 480*(cD+4)^2+426*cD+458
  let Kretire := 10*cD+12
  filter_upwards [selectedAxisPolynomial_le_volume Ktime 2 0,
    selectedAxisPolynomial_le_volume Kstock 2 0,
    selectedAxisPolynomial_le_volume Kretire 2 0] with n ht hs hr
  intro h i D hD
  let p := Sizes.p n
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpSq : p ≤ p^2 := Nat.le_self_pow (by decide) p
  have hDsq := hD.trans (Nat.mul_le_mul_left cD hpSq)
  have hone : 1 ≤ p^2 := hp.trans hpSq
  have hwidth : D+4 ≤ (cD+4)*p := by nlinarith only [hD,hp]
  have hpow := Nat.pow_le_pow_left hwidth 2
  have htable : tblC D 0 ≤ 32*(cD+4)^2*p^2 := by
    unfold tblC
    nlinarith only [hpow]
  have htime : classSetupTimeBound D ≤ Ktime*p^2 := by
    unfold classSetupTimeBound
    dsimp only [Ktime]
    nlinarith only [htable,hDsq,hone]
  have hstock : classSetupStockBound D ≤ Kstock*p^2 := by
    unfold classSetupStockBound
    dsimp only [Kstock]
    nlinarith only [htable,hDsq,hone]
  have hretire : classSetupRetireBound D ≤ Kretire*p^2 := by
    unfold classSetupRetireBound
    dsimp only [Kretire]
    nlinarith only [hDsq,hone]
  exact ⟨htime.trans (by simpa only [pow_zero,mul_one] using ht i),
    hstock.trans (by simpa only [pow_zero,mul_one] using hs i),
    hretire.trans (by simpa only [pow_zero,mul_one] using hr i)⟩

end IntegerMultBounds.MathlibTM2.Cost
