module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicFactorPreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller

/-! Pay the ordinary factor setup at every actual class call, before absorption.
The source lengths and seed banks are produced by the fitting executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open CyclicReplicaPlacement

theorem selectedCyclicFactorPreparationScheduleTime_le {T A : ℕ} (ct scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (jobs : List ι) (ports : CyclicComplexCallerLayout T) (C F : ι → Stacks T A)
      (u target : ℕ) (a n : ι → ℕ),
      jobs.length ≤ 2*Sizes.t m i → u ≤ Sizes.p m → target ≤ ct*Sizes.p m →
      PhaseCellBand.width (Sizes.p m) u ≤ Sizes.s m i →
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let solveTarget := boundaryRecoveryTarget p (target+1)
      (∀ j ∈ jobs, a j ≤ s ∧ n j ≤ s) →
      (∀ j ∈ jobs, ∀ k,
        ((C j).R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span k)).length =
          cyclicFactorMasterValues p l s t u solveTarget (a j) (n j) k) →
      (∀ j ∈ jobs, CyclicFactorSeedInput p l s t u solveTarget (a j) (n j) []
        (embStk (ports.small ∘ factorReg) (F j))) →
      scale*(jobs.map (fun j => ports.factorTimeCost s t p u (a j) (n j) (C j) (F j))).sum ≤ Sizes.T m := by
  let cw := 1032+8*ct
  let copyFactor := 140000*(cw+21)
  let pageFactor := 300000*11^3
  filter_upwards [selectedDistinctCoreSetup_volume_le (copyFactor+pageFactor) 1 3 scale] with m hsetup
  intro ι h i _ jobs ports C F u target a n hcount hu htarget hb
  dsimp only
  intro hgeometry hvalues hseed
  apply hsetup i jobs (fun j => ports.factorTimeCost _ _ _ u (a j) (n j) (C j) (F j)) hcount
  intro j hj
  obtain ⟨ha,hn⟩ := hgeometry j hj
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hw := selectedCyclicWorkingWidth_le ct h i u target (a j) (n j) htarget hb
  have hcopy := cyclicFactorSeedCopyCost_axis
    ((ports.small ∘ factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
    (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span) (C j)
    (Sizes.p m) _ (Sizes.t m i) u _ (a j) (n j) cw (h.good.lt i) hp hl hu hb ha hn hw (hvalues j hj)
  have seed := hseed j hj
  have hpage := prepareCyclicBoundaryPageCost_axis
    (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (ports.small ∘ factorReg) (F j))).R
    (Sizes.t m i) _ (a j) (n j) (h.good.lt i) hb ha hn seed.sourceLength seed.origin seed.span
  have htSquare : Sizes.t m i ≤ Sizes.t m i^2 := by nlinarith only [ht]
  have htCube : Sizes.t m i ≤ Sizes.t m i^3 := by
    have hh := Nat.mul_le_mul_left (Sizes.t m i) htSquare
    nlinarith only [htSquare,hh]
  have hcopyScale := Nat.mul_le_mul_right (Sizes.p m) (Nat.mul_le_mul_left copyFactor htCube)
  have hpageScale := Nat.le_mul_of_pos_right (pageFactor*Sizes.t m i^3) hp
  change _ ≤ copyFactor*Sizes.t m i*Sizes.p m at hcopy
  change _ ≤ pageFactor*Sizes.t m i^3 at hpage
  unfold CyclicComplexCallerLayout.factorTimeCost
  simp only [pow_one]
  nlinarith only [hcopy,hpage,hcopyScale,hpageScale]

end IntegerMultBounds.MathlibTM2.Cost
