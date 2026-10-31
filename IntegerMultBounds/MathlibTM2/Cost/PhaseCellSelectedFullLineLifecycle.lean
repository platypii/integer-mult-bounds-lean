module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFullLineGrid

/-! Selected stock of the actual restoring full-period lifecycle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan

private theorem lifecycleStock (setup tape stock payload replicas scalar volume C : ℕ)
    (hl : setup+(31*tape+9+(C+1)*stock) ≤ (C+1)*stock+756*payload+504*replicas+scalar)
    (hg : (C+1)*stock ≤ 1312000*(C+1)*payload+volume)
    (hs : scalar ≤ volume) :
    setup+(31*tape+9+(C+1)*stock) ≤
      (1312000*(C+1)+756)*payload+504*replicas+2*volume := by
  nlinarith only [hl,hg,hs]

theorem selectedFullLineLifecycleStock_le (ct C : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T Q A : ℕ) (U : Type) (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
        (d : ℝ) (u target : ℕ) (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
        (v : HS T Q A U) (S : Stacks T A),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      input.Ready (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs S →
      GridDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d
        (fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs) →
      let r := fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs
      let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
      setupStock (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i) Fs.length+
        (31*tape.length+9+(C+1)*producer.gridStock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) r) ≤
      ((1312000*(C+1)+756)*(1032+8*ct)+504)*(Fs.length*Sizes.s n i*Sizes.p n)+2*Sizes.T n := by
  filter_upwards [selectedFullLineGridStock_scaled_volume_le ct (C+1),
    selectedFullLineScalars_scaled_volume_le ct 1] with n hg hs
  intro h i _ T Q A U input producer d u target Fs v S hu htarget hband hready hr
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let payload := Fs.length*s*inverseFullInputWidth p u l target s t
  have hl := (fullLineLifecycleCosts_le input producer C Fs v S hready (h.good.lt i)).2
  have hgrid := hg h i T Q A producer d u target Fs hu htarget hr
  have hscalar : fullLineStockScalar p u l target s t ≤ Sizes.T n :=
    (le_max_right _ _).trans (by simpa only [one_mul] using hs h i u target hu htarget hband)
  have hb := lifecycleStock (setupStock p u l target s t Fs.length)
    (descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]).length
    (producer.gridStock p l t r) payload Fs.length (fullLineStockScalar p u l target s t)
    (Sizes.T n) C hl hgrid hscalar
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hw := selectedFullLineWidth_le ct h i u target htarget hband
  have hpay : payload ≤ (1032+8*ct)*(Fs.length*s*p) := by
    have hb := Nat.mul_le_mul_left (Fs.length*s) hw
    simpa only [payload,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb
  have hn : Fs.length ≤ Fs.length*s*p :=
    (Nat.le_mul_of_pos_right _ hspos).trans (Nat.le_mul_of_pos_right _ hp)
  have hpayScaled := Nat.mul_le_mul_left (1312000*(C+1)+756) hpay
  have hnScaled := Nat.mul_le_mul_left 504 hn
  exact hb.trans (by nlinarith only [hpayScaled,hnScaled])

private theorem linearTraffic_le_fast (N K t p band dim : ℕ) (hp : 1 ≤ p) :
    ((K*N*t*p : ℕ) : ℝ) ≤ (N : ℝ)*K*t*(1+(band : ℝ)^2/dim)*(p : ℝ)^(129/128 : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow := Real.self_le_rpow_of_one_le hpR (show (1 : ℝ) ≤ 129/128 by norm_num)
  have hdensity : (1 : ℝ) ≤ 1+(band : ℝ)^2/dim := le_add_of_nonneg_right (by positivity)
  have hscale := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (N : ℝ)*K*t by positivity)
  have hscaleDensity := mul_le_mul_of_nonneg_right hdensity
    (show 0 ≤ (N : ℝ)*K*t*(p : ℝ)^(129/128 : ℝ) by positivity)
  push_cast
  calc
    (K : ℝ)*N*t*p = (N : ℝ)*K*t*p := by ring
    _ ≤ (N : ℝ)*K*t*(p : ℝ)^(129/128 : ℝ) := hscale
    _ ≤ _ := by nlinarith only [hscaleDensity]

private theorem lifecycleTime (total grid payload replicas scalar fast volume : ℕ)
    (hl : total ≤ grid+558*payload+372*replicas+scalar)
    (ht : 558*payload+372*replicas ≤ fast) (hs : scalar ≤ volume) :
    (total : ℝ) ≤ (grid : ℝ)+(fast : ℝ)+(volume : ℝ) := by
  have hb : total ≤ grid+fast+volume := by omega
  exact_mod_cast hb

theorem selectedFullLineLifecycleTime_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T Q A : ℕ) (U : Type) (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
        (d : ℝ) (u target : ℕ) (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
        (v : HS T Q A U) (S : Stacks T A),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      input.Ready (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs S →
      GridDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d
        (fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs) →
      let r := fullLineGridRecord (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) Fs
      let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
      ((setupTime (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i) Fs.length+
        ((r.gridCost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) producer.gridWork+22*tape.length+26)+
          (2*(∑ j, (r.words j).length)+607)) : ℕ) : ℝ) ≤
      2624001*(Sizes.T n : ℝ)+(Fs.length : ℝ)*D*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ)+410 := by
  obtain ⟨D,hD,hg⟩ := selectedFullLineGridCost_fast_le ct
  let K := 558*(1032+8*ct)+372
  refine ⟨D+K,add_nonneg hD (Nat.cast_nonneg K),?_⟩
  filter_upwards [hg,selectedFullLineScalars_scaled_volume_le ct 1] with n hg hs
  intro h i _ T Q A U input producer d u target Fs v S hu htarget hband hready hr
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let payload := Fs.length*s*inverseFullInputWidth p u l target s t
  have hl := (fullLineLifecycleCosts_le input producer 0 Fs v S hready (h.good.lt i)).1
  have hgrid := hg h i T A producer.gridWork d u target Fs hu htarget hr
  have hscalar : fullLineTimeScalar p u l target s t ≤ Sizes.T n :=
    (le_max_left _ _).trans (by simpa only [one_mul] using hs h i u target hu htarget hband)
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have ht : 1 ≤ t := hp.trans (selectedPrecision_le_axis h i)
  have hw := selectedFullLineWidth_le ct h i u target htarget hband
  have hst : s ≤ t := (h.good.lt i).le
  have hpay : payload ≤ (1032+8*ct)*(Fs.length*t*p) := by
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left Fs.length hst) hw
    simpa only [payload,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hb
  have hn : Fs.length ≤ Fs.length*t*p :=
    (Nat.le_mul_of_pos_right _ ht).trans (Nat.le_mul_of_pos_right _ hp)
  have htraffic : 558*payload+372*Fs.length ≤ K*Fs.length*t*p := by
    have hpayScaled := Nat.mul_le_mul_left 558 hpay
    have hnScaled := Nat.mul_le_mul_left 372 hn
    dsimp only [K]
    nlinarith only [hpayScaled,hnScaled]
  have htotalR := lifecycleTime
    (setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*(descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]).length+26)+
        (2*(∑ j, (r.words j).length)+607)))
    (r.gridCost p l t producer.gridWork) payload Fs.length (fullLineTimeScalar p u l target s t)
    (K*Fs.length*t*p) (Sizes.T n) hl htraffic hscalar
  have hfast := linearTraffic_le_fast Fs.length K t p (PhaseCellBand.width p u) (Sizes.d n) hp
  calc
    _ ≤ (r.gridCost p l t producer.gridWork : ℝ)+(K*Fs.length*t*p : ℕ)+(Sizes.T n : ℝ) := htotalR
    _ ≤ (2624000*(Sizes.T n : ℝ)+(Fs.length : ℝ)*D*t*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ)+410)+
        ((Fs.length : ℝ)*K*t*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ))+(Sizes.T n : ℝ) :=
      add_le_add (add_le_add hgrid hfast) (le_refl (Sizes.T n : ℝ))
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
