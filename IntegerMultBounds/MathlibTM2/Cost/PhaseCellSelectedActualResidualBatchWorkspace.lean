module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellActualResidualBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Selected volume pays the actual shared residual solve, independent of batch size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {U : Type}

theorem selectedActualResidualBatchWorkspace_le (hQ : SS.states ≤ Q) (cw cW : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ q w N W replicas : ℕ, q ≤ w → w ≤ cw*Sizes.p m →
      N ≤ Sizes.s m i → W ≤ cW*Sizes.p m →
      preparedResidualBatchWorkspace (A := A) (U := U) Empty hQ q w N W replicas ≤
        (cw+12)*replicas*Sizes.t m i*Sizes.p m+Sizes.T m := by
  let push := actualBoundarySolvePushBounds (A := A) (U := U) hQ
  let C := push.normalize+push.unscale+push.reciprocal+push.column+cw+cW+2
  let K := 200000*(ssMulConst+1)
  filter_upwards [selectedAxisPolynomial_le_volume (K*C^4) 4 4] with m hv
  intro h i q w N W replicas hq hw hN hW
  let t := Sizes.t m i
  let p := Sizes.p m
  let Z := C*t*p
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos hC ht) hp
  have hCZ : C ≤ Z := by
    have h₁ := Nat.mul_le_mul_left C ht
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; omega
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ C) : x ≤ Z := by
    have h₁ := Nat.mul_le_mul_right p hc
    have h₂ := Nat.mul_le_mul_left (C*p) ht
    dsimp only [Z]; nlinarith only [hx,h₁,h₂]
  have hwZ := hparam w cw hw (by dsimp only [C]; omega)
  have hWZ := hparam W cW hW (by dsimp only [C]; omega)
  have htp : 1 ≤ t*p := Nat.mul_pos ht hp
  have htZ : t ≤ Z := by
    have h₁ := Nat.mul_le_mul_right t hC
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; nlinarith only [h₁,h₂]
  have hNZ : N ≤ Z := (hN.trans (h.good.lt i).le).trans htZ
  have hzero := actualResidualBatchWorkspace_zero_poly hZ (hq.trans hwZ) hwZ hNZ hWZ
    ((show push.normalize ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.unscale ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.reciprocal ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.column ≤ C by dsimp only [C]; omega).trans hCZ)
  have heq : 200000*(ssMulConst+1)*Z^4 = (K*C^4)*t^4*p^4 := by dsimp only [Z,K]; ring
  rw [heq] at hzero
  have hshared := hzero.trans (hv i)
  have hvolume := Nat.mul_le_mul (hN.trans (h.good.lt i).le) hw
  have hlinear : N*w+12 ≤ (cw+12)*t*p := by nlinarith only [hvolume,htp]
  have hreplicas := Nat.mul_le_mul_left replicas hlinear
  rw [actualResidualBatchWorkspace_eq_shared_add]
  nlinarith only [hshared,hreplicas]

end IntegerMultBounds.MathlibTM2.Cost
