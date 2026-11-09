module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicNormalizationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Selected volume absorbs the actual cyclic normalizer's shared scratch.
Replica traffic retains its explicit linear payload allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCyclicNormalizationWorkspace_zero_le (cq cw scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ q W a L : ℕ, q ≤ cq*Sizes.p n → W ≤ cw*Sizes.p n → a+L ≤ Sizes.s n i →
      q-Sizes.p n+inverseNormalizationShift (Sizes.p n)+(2*Sizes.p n+13) ≤ 2*q+8 →
      scale*PackedRecoveryNormalization.normalizationWorkspace (Sizes.p n) q W a L 0 ≤ Sizes.T n := by
  let c := 32775+cq+cw
  filter_upwards [selectedAxisPolynomial_le_volume (scale*30000000*c^3) 3 3] with n hv
  intro h i q W a L hq hW hinterval hsize
  let p := Sizes.p n
  let t := Sizes.t n i
  let Z := c*t*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hc : 1 ≤ c := by dsimp only [c]; omega
  have hbase : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ hp
  have hparam (x k : ℕ) (hx : x ≤ k*p) (hk : k ≤ c) : x ≤ Z := by
    apply hx.trans
    calc
      k*p ≤ c*p := Nat.mul_le_mul_right p hk
      _ ≤ c*(t*p) := Nat.mul_le_mul_left c hbase
      _ = Z := by dsimp only [Z]; ring
  have hpZ := hparam p 1 (by omega) (by omega)
  have hqZ := hparam q cq hq (by dsimp only [c]; omega)
  have hWZ := hparam W cw hW (by dsimp only [c]; omega)
  have htZ : t ≤ Z := htp.trans (by dsimp only [Z]; nlinarith only [hc,Nat.zero_le (t*p)])
  have haZ : a ≤ Z := (show a ≤ t by have := h.good.lt i; dsimp only [t]; omega).trans htZ
  have hLZ : L ≤ Z := (show L ≤ t by have := h.good.lt i; dsimp only [t]; omega).trans htZ
  have hB : cyclicNormalizationWidth (2^15*p) q ≤ Z := by
    apply hparam _ (32774+cq) ?_ (by dsimp only [c]; omega)
    have hb : Nat.size (2^15*p) ≤ 32768*p := by
      simpa using (Nat.size_le.mpr (Nat.lt_two_pow_self (n := 32768*p)))
    have hbq : Nat.size q ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
    unfold cyclicNormalizationWidth
    nlinarith only [hb,hbq,hq,hp]
  have hZ : 1 ≤ Z := hp.trans hpZ
  have hzero := cyclicNormalizationWorkspace_zero_le hZ hpZ hqZ hWZ haZ hLZ hB hsize
  have hscaled := Nat.mul_le_mul_left scale hzero
  have hvolume := hv i
  have heq : scale*(30000000*Z^3) = (scale*30000000*c^3)*t^3*p^3 := by
    dsimp only [Z]; ring
  rw [heq] at hscaled
  exact hscaled.trans hvolume

theorem selectedCyclicNormalizationWorkspace_le (cq cw : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ q W a L N : ℕ, q ≤ cq*Sizes.p n → W ≤ cw*Sizes.p n → Sizes.p n ≤ W →
      a+L ≤ Sizes.s n i →
      q-Sizes.p n+inverseNormalizationShift (Sizes.p n)+(2*Sizes.p n+13) ≤ 2*q+8 →
      PackedRecoveryNormalization.normalizationWorkspace (Sizes.p n) q W a L N ≤
        (32*cq+1800)*N*(L+1)*(W+1)+Sizes.T n := by
  filter_upwards [selectedCyclicNormalizationWorkspace_zero_le cq cw 1] with n hz
  intro h i q W a L N hq hW hpW hinterval hsize
  have hzero := hz h i q W a L hq hW hinterval hsize
  simp only [one_mul] at hzero
  have hreplica := Nat.mul_le_mul_left N (cyclicNormalizationReplicaWorkspace_le cq (Sizes.p n) q W L hq hpW)
  rw [cyclicNormalizationWorkspace_eq_shared_add]
  nlinarith only [hzero,hreplica]

end IntegerMultBounds.MathlibTM2.Cost
