module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellScaledFactorWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageWorkspaceBound

/-! The actual scale-two numerical factorization fits selected global volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {U : Type}

theorem selectedScaledInitializedBoundaryFactorWorkspace_le (hQ : SS.states ≤ Q)
    (cq cb scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ q band N : ℕ, q ≤ cq*Sizes.p m → band ≤ cb*Sizes.p m → N ≤ Sizes.s m i →
      scale*scaledInitializedBoundaryFactorWorkspace (P := Empty) (A := A) (U := U)
        2 hQ (Sizes.p m) q band N ≤ Sizes.T m := by
  let C := closedBoundaryFactorWorkspaceCoefficient (A := A) (U := U) hQ
  let K := 102+2*cq+24*cb
  filter_upwards [selectedAxisPolynomial_le_volume (scale*C*K^3) 3 3] with m hv
  intro h i q band N hq hb hN
  let t := Sizes.t m i
  let p := Sizes.p m
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hbase : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have hNp : N ≤ t*p := (hN.trans (h.good.lt i).le).trans (Nat.le_mul_of_pos_right _ hp)
  have hunit : 1 ≤ t*p := Nat.mul_pos ht hp
  have hscaled := Nat.mul_le_mul_left (1+2*cq+24*cb) hbase
  have hR : p+2*q+24*band+N+100 ≤ K*t*p := by
    dsimp only [K]
    nlinarith only [hq,hb,hscaled,hNp,hunit]
  have hpoly := scaledInitializedBoundaryFactorWorkspace_two_poly (A := A) (U := U) hQ p q band N
  have hmono := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hR 3)
  have hbound := Nat.mul_le_mul_left scale (hpoly.trans hmono)
  have heq : scale*(C*(K*t*p)^3) = (scale*C*K^3)*t^3*p^3 := by ring
  rw [heq] at hbound
  exact hbound.trans (hv i)

theorem selectedScaledFactorPageWorkspace_le (cq cb : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ q band N : ℕ, q ≤ cq*Sizes.p m → band ≤ cb*Sizes.p m → N ≤ Sizes.s m i →
      scaledGeneratedFactorPageWorkspace 24 q band N ≤ Sizes.T m := by
  let C := 14000000*(cb+2)*(cb+1)*(cq+1)
  filter_upwards [selectedAxisPolynomial_le_volume C 3 1] with m hv
  intro h i q band N hq hb hN
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have hbase : Sizes.p m ≤ Sizes.t m i*Sizes.p m := Nat.le_mul_of_pos_left _ ht
  have hsmall := Nat.mul_le_mul_left cb hbase
  have hNt : N ≤ Sizes.t m i := hN.trans (h.good.lt i).le
  have htp : Sizes.t m i ≤ Sizes.t m i*Sizes.p m := Nat.le_mul_of_pos_right _ hp
  have hunit : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hrows : N+band+1 ≤ (cb+2)*Sizes.t m i*Sizes.p m := by
    nlinarith only [hNt,hb,hsmall,htp,hunit]
  have hband : band+1 ≤ (cb+1)*Sizes.p m := by nlinarith only [hb,hp]
  have hprecision : q+1 ≤ (cq+1)*Sizes.p m := by nlinarith only [hq,hp]
  have hshape := Nat.mul_le_mul (Nat.mul_le_mul hrows hband) hprecision
  have hpub := scaledGeneratedFactorPageWorkspace24_le q band N
  have hscaled := Nat.mul_le_mul_left 14000000 hshape
  have heq : 14000000*(((cb+2)*Sizes.t m i*Sizes.p m)*((cb+1)*Sizes.p m)*((cq+1)*Sizes.p m)) =
      C*Sizes.t m i^1*Sizes.p m^3 := by dsimp only [C]; ring
  rw [heq] at hscaled
  have hbound : scaledGeneratedFactorPageWorkspace 24 q band N ≤ C*Sizes.t m i^1*Sizes.p m^3 := by
    nlinarith only [hpub,hscaled]
  exact hbound.trans (hv i)

end IntegerMultBounds.MathlibTM2.Cost
