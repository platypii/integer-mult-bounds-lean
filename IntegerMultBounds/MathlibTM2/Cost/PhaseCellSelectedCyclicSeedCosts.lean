module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicSeedCosts
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Absorb generated masters at the actual class frequency, while bounding
one callback's extra workspace independently of replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem cyclicSeedCosts_axis (cZ : ℕ) (hcZ : 1 ≤ cZ) {m : ℕ}
    (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
    (B u l target a n : ℕ)
    (hB : B ≤ cZ*Sizes.p m) (hu : u ≤ cZ*Sizes.p m) (hl : l ≤ cZ*Sizes.p m)
    (htarget : target ≤ cZ*Sizes.p m) (hfit : a+n ≤ Sizes.s m i)
    (hband : PhaseCellBand.width (Sizes.p m) u ≤ cZ*Sizes.p m) :
    CyclicSeedLayout.timeCost B (Sizes.p m) u l target (Sizes.s m i) (Sizes.t m i) a n+
        (2*(List.ofFn (inverseMasterValues (Sizes.p m) u l target (Sizes.s m i) (Sizes.t m i) a (a+n))).sum+21) ≤
      ((60000*32768^3+1000000)*cZ^3)*Sizes.t m i^3*Sizes.p m^3 ∧
    CyclicSeedLayout.workspace B (Sizes.p m) u l target (Sizes.s m i) (Sizes.t m i) a n ≤
      ((60000*32768^3+1000000)*cZ^3)*Sizes.t m i^3*Sizes.p m^3 := by
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hcp : 1 ≤ cZ*Sizes.p m := by simpa using Nat.mul_le_mul hcZ hp
  have hsmall : cZ*Sizes.p m ≤ cZ*Sizes.t m i*Sizes.p m := by
    have hm := Nat.mul_le_mul_left (cZ*Sizes.p m) ht
    nlinarith only [hm]
  have hpZ : Sizes.p m ≤ cZ*Sizes.t m i*Sizes.p m :=
    (show Sizes.p m ≤ cZ*Sizes.p m by simpa using Nat.mul_le_mul_right (Sizes.p m) hcZ).trans hsmall
  have htZ : Sizes.t m i ≤ cZ*Sizes.t m i*Sizes.p m := by
    have hm := Nat.mul_le_mul_left (Sizes.t m i) hcp
    nlinarith only [hm]
  have hb := cyclicSeedCosts_poly (hcp.trans hsmall) (hB.trans hsmall) hpZ
    (hu.trans hsmall) (hl.trans hsmall) (htarget.trans hsmall)
    ((h.good.lt i).le.trans htZ) htZ hfit (hband.trans hsmall)
  have heq : (60000*32768^3+1000000)*(cZ*Sizes.t m i*Sizes.p m)^3 =
      ((60000*32768^3+1000000)*cZ^3)*Sizes.t m i^3*Sizes.p m^3 := by ring
  simpa only [heq] using hb

theorem selectedCyclicSeedScheduleTime_le (cZ scale : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (jobs : List ι) (B u l target : ℕ) (a n : ι → ℕ),
      jobs.length ≤ 2*Sizes.t m i → B ≤ cZ*Sizes.p m → u ≤ cZ*Sizes.p m →
      l ≤ cZ*Sizes.p m → target ≤ cZ*Sizes.p m →
      PhaseCellBand.width (Sizes.p m) u ≤ cZ*Sizes.p m →
      (∀ j ∈ jobs, a j+n j ≤ Sizes.s m i) →
      scale*(jobs.map (fun j => CyclicSeedLayout.timeCost B (Sizes.p m) u l target
        (Sizes.s m i) (Sizes.t m i) (a j) (n j)+
        (2*(List.ofFn (inverseMasterValues (Sizes.p m) u l target (Sizes.s m i) (Sizes.t m i)
          (a j) (a j+n j))).sum+21))).sum ≤ Sizes.T m := by
  filter_upwards [selectedDistinctCoreSetup_volume_le ((60000*32768^3+1000000)*cZ^3) 3 3 scale] with m hsetup
  intro ι h i _ jobs B u l target a n hcount hB hu hl htarget hband hfit
  apply hsetup i jobs _ hcount
  intro j hj
  exact (cyclicSeedCosts_axis cZ hcZ h i B u l target (a j) (n j) hB hu hl htarget (hfit j hj) hband).1

theorem selectedCyclicSeedWorkspace_le (cZ : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (B u l target a n : ℕ), B ≤ cZ*Sizes.p m → u ≤ cZ*Sizes.p m →
      l ≤ cZ*Sizes.p m → target ≤ cZ*Sizes.p m → a+n ≤ Sizes.s m i →
      PhaseCellBand.width (Sizes.p m) u ≤ cZ*Sizes.p m →
      CyclicSeedLayout.workspace B (Sizes.p m) u l target (Sizes.s m i) (Sizes.t m i) a n ≤ Sizes.T m := by
  filter_upwards [selectedAxisPolynomial_le_volume ((60000*32768^3+1000000)*cZ^3) 3 3] with m hvolume
  intro h i _ B u l target a n hB hu hl htarget hfit hband
  exact (cyclicSeedCosts_axis cZ hcZ h i B u l target a n hB hu hl htarget hfit hband).2.trans (hvolume i)

end IntegerMultBounds.MathlibTM2.Cost
