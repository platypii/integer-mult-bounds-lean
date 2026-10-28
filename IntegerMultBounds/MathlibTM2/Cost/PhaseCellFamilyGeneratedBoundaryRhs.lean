module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyGeneratedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryRhs

/-! Price the complete family RHS, including scalar header installation/release
and transfer into the retained factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem familyGeneratedBoundaryRhs_selected_fast_le (cP cq : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (P q u band a b : ℕ),
      P ≤ cP*Sizes.p n → q ≤ cq*Sizes.p n → u ≤ Sizes.t n i →
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      familyGeneratedBoundaryRhsCost P q (Sizes.s n i) (Sizes.t n i) u band a b ≤
        C*Sizes.t n i*Sizes.p n := by
  obtain ⟨K,hK⟩ := generatedBoundaryRhs_selected_fast_le (2*cq+8)
  refine ⟨K+6*cP+18*cq+36+77+4*(2*cq+8)+4,?_⟩
  intro n h i P q u band a b hP hq hu hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hst : s ≤ t := Nat.le_of_lt (h.good.lt i)
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [s,t] at *; omega
  have hw : 2*q+8 ≤ (2*cq+8)*p := by nlinarith only [hq,hp]
  have hm := hK n h i band a b (2*q+8) hband ha hb hw
  have hpt : p ≤ t*p := by simpa using Nat.mul_le_mul_right p ht
  have htp : t ≤ t*p := by simpa using Nat.mul_le_mul_left t hp
  have hP' : P ≤ cP*(t*p) := hP.trans (Nat.mul_le_mul_left cP hpt)
  have hq' : q ≤ cq*(t*p) := hq.trans (Nat.mul_le_mul_left cq hpt)
  have hs' : s ≤ t*p := hst.trans htp
  have hu' : u ≤ t*p := hu.trans htp
  have hb' : band ≤ t*p := hband.trans hs'
  have ha' : a ≤ t*p := ha.trans hs'
  have hbb' : b ≤ t*p := hb.trans hs'
  have hprod := Nat.mul_le_mul hst hw
  have hunit : 1 ≤ t*p := ht.trans htp
  dsimp only [familyGeneratedBoundaryRhsCost,closedGeneratedBoundaryRhsCost,
    installCouplingHeadersCost,releaseCouplingHeadersCost]
  change _ ≤ _*t*p
  nlinarith only [hm,hP',hq',hs',htp,hu',hb',ha',hbb',hprod,hunit]

end IntegerMultBounds.MathlibTM2.Cost
