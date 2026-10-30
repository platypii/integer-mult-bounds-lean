module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedGeometryWorkspaceCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedFactorCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedPreparedCost

/-! The geometry caller's shared workspace fits selected global volume. The
replica-dependent archive allowance is accounted for separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedHaloGeometryWorkspace_zero_poly_le (ct cv : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V coreWidth k radius : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      packedHaloGeometryWorkspace (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) a b V (boundaryRecoveryTarget (Sizes.p n) (target+1))
        (target+1) 2 coreWidth k radius 0 ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨Csetup,hsetup⟩ := selectedPackedHaloSetupReleaseCost_poly_le ct cv
  obtain ⟨Csolve,hsolve⟩ := selectedPackedPreparedInputCost_poly_le ct cv
  obtain ⟨cw,hcw,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cZ := cw+cv+1
  let K := 10000*cZ^2
  refine ⟨Csetup+Csolve+K,?_⟩
  filter_upwards [hsetup,hsolve] with n hs hn
  intro h i _ u target a b V coreWidth k radius hu htarget hab hb hband hV hhalo
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  obtain ⟨hpt,hN,hq,hw,hG,hW,hbandP⟩ := hwidths n h i u target a b htarget hband
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hwScale : cw*p ≤ Z := Nat.mul_le_mul_right p (by dsimp only [cZ]; omega)
  have hVZ : V ≤ Z := hV.trans (Nat.mul_le_mul_right p (by dsimp only [cZ]; omega : cv ≤ cZ))
  have hg := packedHaloGeometryWorkspace_zero_le hst p u l (target+1) a b V coreWidth k radius Z hb hZ hVZ hhalo
    (hq.trans hwScale) (hw.trans hwScale)
  have hf := hs h i u target a b V hu htarget hband (hab.trans hb) hb hV
  have hnumerical := hn h i u target a b V hu htarget hab hb hband hV
  have heq : 10000*t*Z^2 = K*t*p^2 := by dsimp only [Z,K]; ring
  rw [heq] at hg
  have htime : t^5 ≤ t^6 := Nat.pow_le_pow_right ht (by decide)
  have hsolveScale := Nat.mul_le_mul_left (Csolve*p^4) htime
  have htpow : t ≤ t^6 := Nat.le_self_pow (by decide) t
  have hppow : p^2 ≤ p^4 := Nat.pow_le_pow_right hp (by decide)
  have hcontrolScale := Nat.mul_le_mul_left K (Nat.mul_le_mul htpow hppow)
  nlinarith only [hg,hf,hnumerical,hsolveScale,hcontrolScale]

theorem selectedPackedHaloGeometryWorkspace_zero_scaled_volume_le (ct cv scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V coreWidth k radius : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      scale*packedHaloGeometryWorkspace (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) a b V (boundaryRecoveryTarget (Sizes.p n) (target+1))
        (target+1) 2 coreWidth k radius 0 ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedPackedHaloGeometryWorkspace_zero_poly_le ct cv
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 4 6] with n hc hv
  intro h i _ u target a b V coreWidth k radius hu ht hab hb hband hV hhalo
  exact (Nat.mul_le_mul_left scale (hc h i u target a b V coreWidth k radius hu ht hab hb hband hV hhalo)).trans
    (by convert hv i using 1 <;> ring)

/-- Arbitrarily many replicas add only their affine storage bill; all shared
numerical and factor work still fits one selected volume allowance. -/
theorem selectedPackedHaloGeometryWorkspace_scaled_volume_add_replicas_le (ct cv scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V coreWidth k radius count : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      scale*packedHaloGeometryWorkspace p u l s t a b V (boundaryRecoveryTarget p (target+1))
        (target+1) 2 coreWidth k radius count ≤
        scale*count*(4+100*((coreLength s coreWidth k+2*radius)*w+1))+Sizes.T n := by
  filter_upwards [selectedPackedHaloGeometryWorkspace_zero_scaled_volume_le ct cv scale] with n hn
  intro h i _ u target a b V coreWidth k radius count hu ht hab hb hband hV hhalo
  dsimp only
  rw [packedHaloGeometryWorkspace_affine]
  have hzero := hn h i u target a b V coreWidth k radius hu ht hab hb hband hV hhalo
  nlinarith only [hzero]

end IntegerMultBounds.MathlibTM2.Cost
