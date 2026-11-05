module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCanonicalPreparationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGatherPreparationCost

/-! The raw caller's shared initialization has one setup allowance and explicit
linear traffic. Dimension-word width remains visible for the root ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def gatherPreparationScalarFactor (ct : ℕ) : ℕ :=
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  10*(ct+26+cB+cW)+34*cB+8*cW+330

/-- Shared scalar setup is charged once, independently of payload traffic. -/
def sharedPreparationAllowance (ct volume p s t D N : ℕ) : ℕ :=
  volume+gatherPreparationScalarFactor ct*t*(D+p)+(60*(1032+8*ct))*(N*s*p)+N*(4*D+14)

theorem selectedGatherPreparationCost_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target D N radius width Vg Vr : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i)
    (hradius : radius ≤ Sizes.s n i) (hwidth : width ≤ Sizes.s n i)
    (hVg : Vg ≤ D) (hVr : Vr ≤ D) :
    gatherPreparationCost D (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
      (Sizes.s n i) (Sizes.t n i)
      (inverseCallerWordWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        target (Sizes.s n i) (Sizes.t n i))
      (packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) u (target+1) 2) N radius width Vg Vr ≤
      gatherPreparationScalarFactor ct*Sizes.t n i*(D+Sizes.p n)+N*(4*D+14) := by
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let B := inverseCallerWordWidth p u l target s t
  let W := packedHaloCommonWidth p l s u (target+1) 2
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have ht : 1 ≤ t := hp.trans hpt
  have hst : s ≤ t := (h.good.lt i).le
  have hB : B ≤ cB*p := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hW : W ≤ cW*p := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hscan : p+u+l+target+s+t+B+W+radius+width ≤ (ct+26+cB+cW)*t := by
    have huT := hu.trans hpt
    have htargetT := htarget.trans (Nat.mul_le_mul_left ct hpt)
    have hlT := hl.trans (Nat.mul_le_mul_left 20 hpt)
    have hBT := hB.trans (Nat.mul_le_mul_left cB hpt)
    have hWT := hW.trans (Nat.mul_le_mul_left cW hpt)
    have hrT := hradius.trans hst
    have hwT := hwidth.trans hst
    nlinarith only [hpt,huT,htargetT,hlT,hBT,hWT,hst,hrT,hwT]
  have hword : 4*D+10 ≤ 10*(D+p) := by omega
  have hprod := Nat.mul_le_mul hscan hword
  have hD : D ≤ t*(D+p) := by nlinarith only [ht]
  have hpT : p ≤ t*(D+p) := by nlinarith only [ht]
  have hB' := hB.trans (Nat.mul_le_mul_left cB hpT)
  have hW' := hW.trans (Nat.mul_le_mul_left cW hpT)
  have hsW : s*W ≤ cW*t*(D+p) := by
    calc
      s*W ≤ t*(cW*p) := Nat.mul_le_mul hst hW
      _ ≤ t*(cW*(D+p)) := Nat.mul_le_mul_left t
        (Nat.mul_le_mul_left cW (Nat.le_add_left p D))
      _ = cW*t*(D+p) := by ring
  have hs : s ≤ t*(D+p) := by nlinarith only [hst,hp]
  have hone : 1 ≤ t*(D+p) := hp.trans hpT
  have hc := gatherPreparationCost_le D p u l target s t B W N radius width Vg Vr hVg hVr
  change gatherPreparationCost D p u l target s t B W N radius width Vg Vr ≤ _
  dsimp only [gatherPreparationScalarFactor]
  dsimp only [cB,cW,p,s,t,l,B,W] at hc hprod hD hB' hW' hsW hs hone ⊢
  nlinarith only [hc,hprod,hD,hB',hW',hsW,hs,hone]

theorem selectedSharedBoundaryPreparationTime_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target D N radius width Vg Vr : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      radius ≤ Sizes.s n i → width ≤ Sizes.s n i → Vg ≤ D → Vr ≤ D →
      sharedBoundaryPreparationTime (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
        (Sizes.s n i) (Sizes.t n i) D N radius width Vg Vr ≤
        sharedPreparationAllowance ct (Sizes.T n) (Sizes.p n) (Sizes.s n i) (Sizes.t n i) D N := by
  filter_upwards [selectedCanonicalInputPreparationTime_le ct] with n hn
  intro h i _ u target D N radius width Vg Vr hu htarget hband hradius hwidth hVg hVr
  have hc := hn h i u target N hu htarget hband
  have hg := selectedGatherPreparationCost_le ct h i u target D N radius width Vg Vr
    hu htarget hband hradius hwidth hVg hVr
  dsimp only [sharedBoundaryPreparationTime,sharedPreparationAllowance]
  omega

end IntegerMultBounds.MathlibTM2.Cost
