module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellWeightSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing

/-! The entire executed numerical weight family has linear axis-volume and
quartic precision setup cost, uniformly over the selected axes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedWeightFamilySetup_poly_le (cw cl : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A N q l u band a b : ℕ,
      N ≤ cw*Sizes.p n → 2*q+8 ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n → u ≤ Sizes.p n →
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      prepareHaloWeightFamilyCost A (2^15*Sizes.p n) N q l (Sizes.s n i) (Sizes.t n i) u band a b ≤
        C*Sizes.t n i*(Sizes.p n)^4 := by
  let cZ := 2^15+3*cw+cl+426016
  obtain ⟨C,hC⟩ := selectedLengthKeyInitialization_fast_le cw cw cl
  refine ⟨C+13000000*cZ^4,?_⟩
  intro n h i _ A N q l u band a b hN hw hl hu hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hq : q ≤ cw*p := (show q ≤ 2*q+8 by omega).trans hw
  have hinit := hC n h i N q l u band a b hN hq hl hu hband ha hb
  have hv := selectedWeightWorkspaceWidth_le cw h i q (2*q+8) u hw (by omega) hu
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p hc)
  have hPZ := hparam (2^15*p) (2^15) le_rfl (by dsimp only [cZ]; omega)
  have hNZ := hparam N cw hN (by dsimp only [cZ]; omega)
  have hqZ := hparam q cw hq (by dsimp only [cZ]; omega)
  have hlZ := hparam l cl hl (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa using hu) (by dsimp only [cZ]; omega)
  have hwZ := hparam (2*q+8) cw hw (by dsimp only [cZ]; omega)
  have hVZ := hparam _ (2*cw+426009) hv (by dsimp only [cZ]; omega)
  have hcell := phaseGap_cellLength_le hp hst (h.quarter_p_le_theta i)
  have hkeys : ∀ L ∈ haloLengthKeys s t band a b, L ≤ Z := by
    intro L hL
    have hc := List.mem_dedup.mp (List.mem_filter.mp hL).1
    have hlen := haloLengthCandidates_uniform hst band a b hc
    apply hparam L 5 (by omega)
    dsimp only [cZ]; omega
  have hcost := prepareHaloWeightFamilyCost_poly A hZ hst hPZ hNZ hqZ hlZ huZ hwZ
    (hband.trans hst.le) (ha.trans hst.le) (hb.trans hst.le) hVZ hkeys
  have hp4 : p ≤ p^4 := by simpa using Nat.pow_le_pow_right hp (show 1 ≤ 4 by decide)
  have hscale := Nat.mul_le_mul_left (C*t) hp4
  have heq : Z^4 = cZ^4*p^4 := by dsimp only [Z]; exact mul_pow _ _ _
  rw [heq] at hcost
  nlinarith only [hcost,hinit,hscale]

end IntegerMultBounds.MathlibTM2.Cost
