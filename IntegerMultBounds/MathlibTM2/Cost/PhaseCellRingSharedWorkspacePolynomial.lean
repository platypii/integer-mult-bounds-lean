module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixedStock

/-! The packed ring primitive retains only polynomial shared scratch at zero batch size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- A deliberately coarse polynomial is enough for a one-time shared reserve. -/
theorem rpRingBound_poly {N Z : ℕ} (hZ : 1 ≤ Z) (hN : N ≤ Z) :
    rpRingBound N ≤ (32*costC cA cB cC0+300000)*Z^5 := by
  have hb : bitlen N ≤ Z := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hN
  have hc : bitlen (bitlen N^3) ≤ Z^3 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left hb 3)
  have hZ3 : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have hm : rpRingBound N ≤ 4*costC cA cB cC0*(2*Z)*(2*Z)*(2*Z^3)+11000*Z+250000 := by
    unfold rpRingBound
    gcongr <;> omega
  have h1 : Z ≤ Z^5 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^5 := Nat.one_le_pow _ _ hZ
  nlinarith only [hm,h1,h0]

theorem rpWorkspace_zero_le_cost (p l w : ℕ) :
    rpWorkspace p l w 0 ≤ 100*(rpFixCost p l w+rpRecCost p l w+1) := by
  unfold rpWorkspace rpHostWorkspace ringCoreWorkspace ringSharedBankStock ringConstantStock
    ringRecordCost rpFixCost rpRecCost
  dsimp only
  ring_nf
  omega

@[irreducible] noncomputable def ringSharedWorkspaceConstant : ℕ :=
  100*(mtCvKf 10+3*(32*costC cA cB cC0+300000)*10^5+4001)

theorem rpWorkspace_zero_poly {p l w Z : ℕ} (hZ : 1 ≤ Z) (hp : 1 ≤ p)
    (hl : l ≤ p) (hw : w ≤ 10*p) (hpZ : p ≤ Z) (hlZ : l ≤ Z)
    (hwZ : w ≤ Z) (hrZ : 2^l ≤ Z) :
    rpWorkspace p l w 0 ≤ ringSharedWorkspaceConstant*Z^10 := by
  unfold ringSharedWorkspaceConstant
  generalize hcost : costC cA cB cC0 = B at ⊢
  generalize hfixConst : mtCvKf 10 = F at ⊢
  have hW : wOf p l w ≤ 10*Z := by
    have hh := mt_cv_wOf_le p l w hp
    omega
  have hN : wOf p l w*2^l ≤ 10*Z^2 := by
    have hh := Nat.mul_le_mul hW hrZ
    nlinarith only [hh]
  have hR := rpRingBound_poly (by have := Nat.one_le_pow 2 Z hZ; omega : 1 ≤ 10*Z^2) hN
  rw [hcost] at hR
  have hrec := rpRecCost_le p l w
  have hfix := mt_cv_fix_le hp hl hw hrZ hpZ
  rw [hfixConst] at hfix
  have hprod : Z*p ≤ Z^2 := by simpa only [pow_two] using Nat.mul_le_mul_left Z hpZ
  have h2 : Z^2 ≤ Z^10 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^10 := Nat.one_le_pow _ _ hZ
  have hfix' : rpFixCost p l w ≤ F*Z^10 := by
    have hh := Nat.mul_le_mul_left F (hprod.trans h2)
    nlinarith only [hfix,hh]
  have hrec' : rpRecCost p l w ≤
      (3*(32*B+300000)*10^5+4000)*Z^10 := by
    have hm : rpRecBound p l w ≤
        3*((32*B+300000)*(10*Z^2)^5+Z*(180*Z+400)+204)+100*(Z*Z) := by
      unfold rpRecBound
      gcongr
    have h1 : Z ≤ Z^10 := Nat.le_self_pow (by decide) Z
    nlinarith only [hrec,hm,h2,h1,h0]
  have hs := rpWorkspace_zero_le_cost p l w
  change _ ≤ 100*(F+3*(32*B+300000)*10^5+4001)*Z^10
  nlinarith only [hs,hfix',hrec',h0]

theorem ringBatchSetupCost_poly {p l w Z : ℕ} (hZ : 1 ≤ Z)
    (hpZ : p ≤ Z) (hlZ : l ≤ Z) (hwZ : w ≤ Z) (hrZ : 2^l ≤ Z) :
    batchSetupCost p l w (2^l) (2^l) ≤ 1000*Z^2 := by
  have hsetup : batchSetupCost p l w (2^l) (2^l) ≤
      (Z*(4*Z+9)+4+(4*Z+4*(Z*Z)+9*Z+4*(Z*Z)+12))+
      (Z*(4*Z+9)+4+(4*Z+4*(Z*Z)+9*Z+4*(Z*Z)+12))+(23*Z+8*Z+23*Z+35) := by
    unfold batchSetupCost operandSetupCost ldrHeaderCost
    gcongr
  have h1 : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^2 := Nat.one_le_pow _ _ hZ
  nlinarith only [hsetup,h1,h0]

theorem fixedWorkspace_zero_eq (C p l w : ℕ) :
    Fixed.workspace C p l w 0 = 3*batchSetupCost p l w (2^l) (2^l)+(C+1)*rpWorkspace p l w 0+48 := by
  have hform (B V r : ℕ) :
      3*B+(C+1)*V+(1842*(C+1)+120)*(0*r*w)+150*0+48 = 3*B+(C+1)*V+48 := by
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero]
  exact hform (batchSetupCost p l w (2^l) (2^l)) (rpWorkspace p l w 0) (2^l)


theorem fixedWorkspace_zero_le_of_ring {C p l w S Z : ℕ} (hZ : 1 ≤ Z)
    (hC : C ≤ Z) (hpZ : p ≤ Z) (hlZ : l ≤ Z) (hwZ : w ≤ Z) (hrZ : 2^l ≤ Z)
    (hr : rpWorkspace p l w 0 ≤ S*Z^10) :
    Fixed.workspace C p l w 0 ≤ (2*S+4000)*Z^11 := by
  have hsetup' := ringBatchSetupCost_poly hZ hpZ hlZ hwZ hrZ
  have hC' : C+1 ≤ 2*Z := by omega
  have hm := Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 3 hsetup') (Nat.mul_le_mul hC' hr)) 48
  have h2 : Z^2 ≤ Z^11 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^11 := Nat.one_le_pow _ _ hZ
  rw [fixedWorkspace_zero_eq]
  calc
    _ ≤ 3*(1000*Z^2)+(2*Z)*(S*Z^10)+48 := hm
    _ ≤ 3*(1000*Z^11)+(2*Z)*(S*Z^10)+48*Z^11 := by
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 1000 h2)) _)
        (by simpa using Nat.mul_le_mul_left 48 h0)
    _ = (3*1000+2*S+48)*Z^11 := by
      have heq : (2*Z)*(S*Z^10) = (2*S)*Z^11 := by rw [pow_succ (n := 10)]; ac_rfl
      rw [heq,←Nat.mul_assoc,←Nat.add_mul,←Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem fixedWorkspace_zero_poly {C p l w Z : ℕ} (hZ : 1 ≤ Z) (hC : C ≤ Z)
    (hp : 1 ≤ p) (hl : l ≤ p) (hw : w ≤ 10*p) (hpZ : p ≤ Z) (hlZ : l ≤ Z)
    (hwZ : w ≤ Z) (hrZ : 2^l ≤ Z) :
    Fixed.workspace C p l w 0 ≤ (2*ringSharedWorkspaceConstant+4000)*Z^11 :=
  fixedWorkspace_zero_le_of_ring hZ hC hpZ hlZ hwZ hrZ
    (rpWorkspace_zero_poly hZ hp hl hw hpZ hlZ hwZ hrZ)

end IntegerMultBounds.MathlibTM2.Cost
