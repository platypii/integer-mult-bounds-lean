module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedNormalizationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedGeometryWorkspace

/-! Complete selected shared workspace for the actual normalized local caller.
The numerical and factor allowance is independent of the replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedNormalizedWorkspace_zero_poly_le (ct cv cB cW : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ B W u target a b V coreWidth k radius : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      B ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      packedKeyNormalizedWorkspace B p q W u l s t a b V (boundaryRecoveryTarget p (target+1))
        (target+1) 2 target coreWidth k radius 0 ≤ C*t^6*p^4 := by
  obtain ⟨C,hgeometry⟩ := selectedPackedHaloGeometryWorkspace_zero_poly_le ct cv
  obtain ⟨cw,hcw,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cZ := cw+cv+cB+cW+1
  let K := 2000000*cZ^3
  refine ⟨C+K,?_⟩
  filter_upwards [hgeometry] with n hn
  intro h i _ B W u target a b V coreWidth k radius hu htarget hab hb hband hV hB hW hhalo
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  obtain ⟨hpt,hN,hq,hw,hG,hrowWidth,hbandP⟩ := hwidths n h i u target a b htarget hband
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z := hx.trans (Nat.mul_le_mul_right p hc)
  have hBZ := hparam B cB hB (by dsimp only [cZ]; omega)
  have hWZ := hparam W cW hW (by dsimp only [cZ]; omega)
  have hpZ := hparam p 1 (by omega) (by dsimp only [cZ]; omega)
  have hqZ := hparam q cw hq (by dsimp only [cZ]; omega)
  have hbandZ := hparam band cw hbandP (by dsimp only [cZ]; omega)
  have hwZ := hparam _ cw hw (by dsimp only [cZ]; omega)
  have hwidth : executionWidth p l stage 2 = 2*q+8 := by dsimp only [q,executionWidth,executionPrecision]; omega
  change executionWidth p l stage 2 ≤ Z at hwZ
  rw [hwidth] at hwZ
  have hqE : q = 4*inverseExecutionExponent p l target N band := by
    simpa only [q,stage,bits,N,band,boundaryHaloTarget,Nat.add_sub_cancel] using packedRound_precision p u l target N
  have hnormal : 8*inverseExecutionExponent p l target N band+8 ≤ Z := by omega
  have hnormalized := packedKeyNormalizedWorkspace_zero_le_geometry
    (B := B) (p := p) (q := q) (W := W) (u := u) (l := l) (s := s) (t := t) (a := a) (b := b) (V := V)
    (boundaryTarget := boundaryRecoveryTarget p (target+1)) (finalTarget := target+1) (rhsExp := 2)
    (targetOut := target) (coreWidth := coreWidth) (k := k) (radius := radius)
    ht hZ hst.le hBZ hpZ hqZ hWZ hbandZ hnormal
  have hg := hn h i u target a b V coreWidth k radius hu htarget hab hb hband hV hhalo
  have heq : 2000000*t*Z^3 = K*t*p^3 := by dsimp only [Z,K]; ring
  rw [heq] at hnormalized
  have htpow : t ≤ t^6 := Nat.le_self_pow (by decide) t
  have hppow : p^3 ≤ p^4 := Nat.pow_le_pow_right hp (by decide)
  have hscale := Nat.mul_le_mul_left K (Nat.mul_le_mul htpow hppow)
  nlinarith only [hnormalized,hg,hscale]

theorem selectedPackedNormalizedWorkspace_zero_scaled_volume_le (ct cv cB cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ B W u target a b V coreWidth k radius : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      B ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      scale*packedKeyNormalizedWorkspace B p q W u l s t a b V (boundaryRecoveryTarget p (target+1))
        (target+1) 2 target coreWidth k radius 0 ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedPackedNormalizedWorkspace_zero_poly_le ct cv cB cW
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 4 6] with n hc hv
  intro h i _ B W u target a b V coreWidth k radius hu ht hab hb hband hV hB hW hhalo
  dsimp only
  exact (Nat.mul_le_mul_left scale (hc h i B W u target a b V coreWidth k radius hu ht hab hb hband hV hB hW hhalo)).trans
    (by convert hv i using 1 <;> ring)

/-- The full normalized workspace pays numerical setup and scratch once.
Arbitrarily many replicas contribute only their stored halo volume. -/
theorem selectedPackedNormalizedWorkspace_scaled_volume_add_replicas_le (ct cv cB cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ B W u target a b V coreWidth k radius count : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      B ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      2*q+8 ≤ W →
      scale*packedKeyNormalizedWorkspace B p q W u l s t a b V (boundaryRecoveryTarget p (target+1))
        (target+1) 2 target coreWidth k radius count ≤
        500*scale*count*((b-a)*W+1)+Sizes.T n := by
  filter_upwards [selectedPackedNormalizedWorkspace_zero_scaled_volume_le ct cv cB cW scale] with n hn
  intro h i _ B W u target a b V coreWidth k radius count hu ht hab hb hband hV hB hW hhalo
  dsimp only
  intro hnative
  rw [packedKeyNormalizedWorkspace_affine]
  have hzero := hn h i B W u target a b V coreWidth k radius hu ht hab hb hband hV hB hW hhalo
  have hreplica := packedKeyWorkspaceReplicaCost_le_volume_native (Sizes.p n) _ W u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
    a b target coreWidth k radius hhalo hnative rfl
  have hscaled := Nat.mul_le_mul_left (scale*count) hreplica
  nlinarith only [hzero,hscaled]

end IntegerMultBounds.MathlibTM2.Cost
