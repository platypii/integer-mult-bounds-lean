module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCouplingSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedMaskCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellLengthKeySetup

/-! The whole executed coupling cache setup, including masks and scalar headers,
has linear selected axis volume and quartic precision cost. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCouplingKeySetup_poly_le (cw cB : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u band a b : ℕ),
      2*q+8 ≤ cw*Sizes.p n → u ≤ Sizes.p n → band ≤ cB*Sizes.p n →
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      couplingKeySetupCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b ≤
        C*Sizes.t n i*(Sizes.p n)^4 := by
  let cZ := 3*cw+cB+500000
  let H := 1000000*(cw+cB+1)
  obtain ⟨K,hK⟩ := selectedMasks_fast_le
  refine ⟨2*K+H+4000000*cZ^4,?_⟩
  intro n h i q u band a b hw hu hB hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let w := 2*q+8
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hq : q ≤ cw*p := (show q ≤ 2*q+8 by omega).trans hw
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p hc)
  have hPZ := hparam (2^15*p) (2^15) le_rfl (by dsimp only [cZ]; omega)
  have hqZ := hparam q cw hq (by dsimp only [cZ]; omega)
  have hwZ := hparam w cw hw (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa using hu) (by dsimp only [cZ]; omega)
  have hBZ := hparam band cB hB (by dsimp only [cZ]; omega)
  have hbitsT : Nat.size t ≤ p+1 := by
    have htbits := selectedAxisBits_le n i
    have hell := selectedAxisLog_le_precision h
    dsimp only [p,t] at *
    omega
  have hbitsS : Nat.size s ≤ p+1 := (Nat.size_le_size hst.le).trans hbitsT
  have hbitsB : Nat.size band ≤ p+1 := (Nat.size_le_size (hband.trans hst.le)).trans hbitsT
  have hbitsU : Nat.size u ≤ p := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hu
  have hVZ : liftedCoefficientWidth (2^15*p) q w s t u band ≤ Z := by
    dsimp only [liftedCoefficientWidth,liftedCoefficientSize,Z,cZ]
    dsimp only [p,s,t,w] at *
    nlinarith only [hw,hq,hbitsT,hbitsS,hbitsB,hbitsU,hp]
  have hcache := buildCouplingPageCacheCost_poly (a := a) (b := b)
    ht hZ hst.le hPZ hqZ hwZ huZ hBZ hVZ
  have hpp : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ hp
  have hPp := Nat.mul_le_mul_left (2^15) hpp
  have hqp := hq.trans (Nat.mul_le_mul_left cw hpp)
  have hBp := hB.trans (Nat.mul_le_mul_left cB hpp)
  have hheaders : installCouplingHeadersCost (2^15*p) q s t u band a b+
      releaseCouplingHeadersCost (2^15*p) q s t u band a b ≤ H*t*p := by
    dsimp only [installCouplingHeadersCost,releaseCouplingHeadersCost,H]
    dsimp only [p,s,t] at *
    nlinarith only [hPp,hqp,hBp,hu,hpp,htp,hst,ha,hb,ht]
  have hmask := hK n h i band a b hband ha hb
  have hp4 : p ≤ p^4 := by simpa using Nat.pow_le_pow_right hp (show 1 ≤ 4 by decide)
  have hscale := Nat.mul_le_mul_left ((2*K+H)*t) hp4
  dsimp only [couplingKeySetupCost]
  dsimp only [prepareCouplingGuardCost] at hcache
  dsimp only [p,s,t,w,Z] at hcache hheaders hscale ⊢
  nlinarith only [hcache,hheaders,hmask,hscale]

end IntegerMultBounds.MathlibTM2.Cost
