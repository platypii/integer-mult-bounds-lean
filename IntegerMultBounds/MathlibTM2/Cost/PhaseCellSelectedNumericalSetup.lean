module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNumericalSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellLengthKeySetup

/-! Selected axes absorb fixed polynomial construction costs uniformly in the axis. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedAxis_eventually_polynomial (C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (Sizes.d n), C*(Sizes.p n)^e ≤ Sizes.t n i := by
  filter_upwards [Sizes.eventually_pow_p_le_r (e+1),
    tendsto_atTop.1 Sizes.tendsto_b (2*C)] with n hpow hb
  intro i
  have hcoeff : 2*C ≤ Sizes.p n := by dsimp only [Sizes.p]; omega
  have hmul := Nat.mul_le_mul_right ((Sizes.p n)^e) hcoeff
  have haxis : 2*(C*(Sizes.p n)^e) ≤ Sizes.r n := by
    rw [pow_succ] at hpow
    nlinarith only [hmul,hpow]
  rw [Sizes.t_eq i]
  split_ifs <;> omega

theorem selectedConstructionWidths_le (cP cM cq cL : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) {P M q u band L : ℕ}
    (hP : P ≤ cP*Sizes.p n) (hM : M ≤ cM*Sizes.p n) (hq : q ≤ cq*Sizes.p n)
    (hu : u ≤ Sizes.p n) (hband : band ≤ Sizes.s n i) (hL : L ≤ cL*Sizes.p n) :
    let cW := cP*(cM+2)+cq+5
    let cV := cW+13*cP+2*cL+24
    integerSetupWidth P q (M+1) 0 ≤ cW*(Sizes.p n)^2 ∧
      coefficientWorkspaceWidth P (integerSetupWidth P q (M+1) 0) (Sizes.t n i) u band L ≤
        cV*(Sizes.p n)^2 := by
  dsimp only
  let p := Sizes.p n
  let cW := cP*(cM+2)+cq+5
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hsq : p ≤ p^2 := by nlinarith only [hp]
  have hone : 1 ≤ p^2 := Nat.one_le_pow _ _ hp
  have hM' : M+2 ≤ (cM+2)*p := by dsimp only [p]; nlinarith only [hM,hp]
  have hprod := Nat.mul_le_mul hP hM'
  have hq' := hq.trans (Nat.mul_le_mul_left cq hsq)
  have hW : integerSetupWidth P q (M+1) 0 ≤ cW*p^2 := by
    dsimp only [integerSetupWidth,cW]
    nlinarith only [hprod,hq',hone]
  refine ⟨hW,?_⟩
  have htbits := selectedAxisBits_le n i
  have hell := selectedAxisLog_le_precision h
  have htb : Nat.size (Sizes.t n i) ≤ 2*p := by dsimp only [p]; omega
  have hub : Nat.size u ≤ p := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hu
  have hLb : Nat.size L ≤ cL*p := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hL
  have hst := h.good.lt i
  have hbb : Nat.size band ≤ 2*p := (Nat.size_le_size (hband.trans hst.le)).trans htb
  have hP' := hP.trans (Nat.mul_le_mul_left cP hsq)
  have hLb' := hLb.trans (Nat.mul_le_mul_left cL hsq)
  change coefficientWorkspaceWidth P (integerSetupWidth P q (M+1) 0) (Sizes.t n i) u band L ≤
    (cW+13*cP+2*cL+24)*p^2
  unfold coefficientWorkspaceWidth
  nlinarith only [hW,hP',hLb',htb,hub,hbb,hsq,hone]

theorem selectedHeaderGeneratorSetup_fast_le (cP cM cq cL : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (P M q u band L : ℕ),
      P ≤ cP*Sizes.p n → M ≤ cM*Sizes.p n → q ≤ cq*Sizes.p n →
      u ≤ Sizes.p n → band ≤ Sizes.s n i → L ≤ cL*Sizes.p n →
      headerGeneratorSetupCost P M q (Sizes.s n i) (Sizes.t n i) u band L ≤ C*Sizes.t n i := by
  let cW := cP*(cM+2)+cq+5
  let cV := cW+13*cP+2*cL+24
  let cZ := cV+cP+cM+cq+cL+1
  let K := (1000000*(ssMulConst+1)+10000)*cZ^6
  refine ⟨301,?_⟩
  filter_upwards [selectedAxis_eventually_polynomial K 12] with n hn
  intro h i P M q u band L hP hM hq hu hband hL
  let p := Sizes.p n
  let Z := cZ*p^2
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hsq : p ≤ p^2 := by nlinarith only [hp]
  have hzcoef : 1 ≤ cZ := by dsimp only [cZ]; omega
  have hZ : 1 ≤ Z := by dsimp only [Z]; simpa only [Nat.one_mul] using Nat.mul_le_mul hzcoef (Nat.one_le_pow 2 p hp)
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z :=
    hx.trans ((Nat.mul_le_mul_left c hsq).trans (Nat.mul_le_mul_right (p^2) hc))
  have hPZ := hparam P cP hP (by dsimp only [cZ]; omega)
  have hMZ := hparam M cM hM (by dsimp only [cZ]; omega)
  have hqZ := hparam q cq hq (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa only [one_mul] using hu) hzcoef
  have hLZ := hparam L cL hL (by dsimp only [cZ]; omega)
  obtain ⟨hw,hv⟩ := selectedConstructionWidths_le cP cM cq cL h i hP hM hq hu hband hL
  have hwZ : integerSetupWidth P q (M+1) 0 ≤ Z :=
    hw.trans (Nat.mul_le_mul_right (p^2) (by dsimp only [cZ,cV]; omega : cW ≤ cZ))
  have hvZ : coefficientWorkspaceWidth P (integerSetupWidth P q (M+1) 0) (Sizes.t n i) u band L ≤ Z :=
    hv.trans (Nat.mul_le_mul_right (p^2) (by dsimp only [cZ]; omega : cV ≤ cZ))
  have hc := headerGeneratorSetupCost_poly (s := Sizes.s n i) hZ hPZ hMZ hqZ huZ hLZ hwZ hvZ
  have hpoly : (1000000*(ssMulConst+1)+10000)*Z^6 ≤ Sizes.t n i := by
    have heq : (1000000*(ssMulConst+1)+10000)*Z^6 = K*p^12 := by
      dsimp only [Z,K]
      rw [mul_pow,← pow_mul]
      ring
    rw [heq]
    exact hn i
  have hst := h.good.lt i
  nlinarith only [hc,hpoly,hst,hband]

end IntegerMultBounds.MathlibTM2.Cost
