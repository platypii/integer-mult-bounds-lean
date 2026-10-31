module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFullLineLifecycleLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreHeaderWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup

/-! Full-period setup is one selected scalar charge; payload traffic stays linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFullLineWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (u target : ℕ) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    inverseFullInputWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
      (Sizes.s n i) (Sizes.t n i) ≤ (1032+8*ct)*Sizes.p n := by
  exact selectedInverseWorkingWidth_le ct h i u target 0 (Sizes.s n i) htarget hband

theorem selectedFullLineScalars_le (ct : ℕ) :
    ∃ K : ℕ, ∀ n : ℕ, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (u target : ℕ),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      fullLineTimeScalar (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
        (Sizes.s n i) (Sizes.t n i) ≤ K*Sizes.t n i*Sizes.p n ∧
      fullLineStockScalar (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
        (Sizes.s n i) (Sizes.t n i) ≤ K*Sizes.t n i*Sizes.p n := by
  let cB := 2*(ct+21)+22
  let ctime := (ct+25)*(4*cB+10)+18306*cB+26708
  let cstock := 24758*cB+35610
  refine ⟨ctime+cstock,?_⟩
  intro n h i u target hu htarget hband
  let p := Sizes.p n
  let t := Sizes.t n i
  let s := Sizes.s n i
  let l := haloInverseRingLog s t
  let B := inverseCallerWordWidth p u l target s t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have ht : 1 ≤ t := hp.trans hpt
  have hpT : p ≤ t*p := Nat.le_mul_of_pos_left p ht
  have hB : B ≤ cB*p := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hvalues : p+u+l+target+s+t+0+s ≤ (ct+25)*t := by
    have huT := hu.trans hpt
    have hlT := hl.trans (Nat.mul_le_mul_left 20 hpt)
    have htargetT := htarget.trans (Nat.mul_le_mul_left ct hpt)
    have hst := (h.good.lt i).le
    change s ≤ t at hst
    nlinarith only [hpt,huT,hlT,htargetT,hst]
  have hwidth : 4*B+10 ≤ (4*cB+10)*p := by nlinarith only [hB,hp]
  have hprod := Nat.mul_le_mul hvalues hwidth
  have htimeLinear : 18306*B+26708 ≤ (18306*cB+26708)*t*p := by
    have hs : 18306*B+26708 ≤ (18306*cB+26708)*p := by nlinarith only [hB,hp]
    have hscale := Nat.mul_le_mul_left (18306*cB+26708) hpT
    exact hs.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm] using hscale)
  have htime : fullLineTimeScalar p u l target s t ≤ ctime*t*p := by
    unfold fullLineTimeScalar
    change (p+u+l+target+s+t+0+s)*(4*B+10)+18306*B+26708 ≤ ctime*t*p
    dsimp only [ctime]
    nlinarith only [hprod,htimeLinear]
  have hstockLinear : 24758*B+35610 ≤ (24758*cB+35610)*p := by nlinarith only [hB,hp]
  have hstock : fullLineStockScalar p u l target s t ≤ cstock*t*p :=
    hstockLinear.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,cstock] using Nat.mul_le_mul_left cstock hpT)
  exact ⟨htime.trans (Nat.mul_le_mul_right p (Nat.mul_le_mul_right t (Nat.le_add_right ctime cstock))),
    hstock.trans (Nat.mul_le_mul_right p (Nat.mul_le_mul_right t (Nat.le_add_left cstock ctime)))⟩

theorem selectedFullLineScalars_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (u target : ℕ),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      scale*max
        (fullLineTimeScalar (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i))
        (fullLineStockScalar (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i)) ≤ Sizes.T n := by
  obtain ⟨K,hcost⟩ := selectedFullLineScalars_le ct
  filter_upwards [selectedAxisPolynomial_le_volume (scale*K) 1 1] with n hn
  intro h i u target hu htarget hband
  have hc := hcost n h i u target hu htarget hband
  exact (Nat.mul_le_mul_left scale (max_le hc.1 hc.2)).trans (by
    simpa only [pow_one,Nat.mul_assoc] using hn i)

end IntegerMultBounds.MathlibTM2.Cost
