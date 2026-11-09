module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicOriginTimeLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFactorPreparationSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFittingCyclicInputSchedule

/-! Discharge the ordinary callback overhead over its actual class list.
The established numerical fast-time theorem can then be applied unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  CyclicComplexCallerLayout
open CyclicReplicaPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedCyclicOriginScheduleTime_le {T : ℕ} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct cw cW cV : ℕ) :
    let b := 8*executionPush (A := A) (U := U) hR hQ+1
    let D := 32*cW+2*(4*cW+12*cw+28)+70
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (jobs : List ι) (ports : CyclicComplexCallerLayout T)
      (H K : ι → ReplicaHaloProblem (Sizes.s m i)) (S C F : ι → Stacks T A)
      (u target V W N volume : ℕ) (a n radius core numerical steps : ι → ℕ),
      jobs.length ≤ 2*Sizes.t m i → u ≤ Sizes.p m → target ≤ ct*Sizes.p m →
      PhaseCellBand.width (Sizes.p m) u ≤ Sizes.s m i → V ≤ cV*Sizes.p m → W ≤ cW*Sizes.p m →
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let solveTarget := boundaryRecoveryTarget p (target+1)
      (∀ j ∈ jobs, a j ≤ s ∧ n j ≤ s ∧ radius j+core j ≤ s) →
      (∀ j ∈ jobs, ∀ R ∈ [H j,K j], R.p = p ∧ R.t = t ∧ R.l ≤ 20*p ∧ R.u ≤ p ∧ R.wordWidth ≤ cw*p) →
      (∀ j ∈ jobs, (H j).Fs.length = 2*N ∧ (K j).Fs.length = 2*N) →
      (∀ j ∈ jobs,
        (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedL k)).length = recoverySeedHeader (H j) W N k) ∧
        (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedR k)).length = recoverySeedHeader (K j) W N k)) →
      (∀ j ∈ jobs, ∀ k, ((C j).R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span k)).length =
        cyclicFactorMasterValues p l s t u solveTarget (a j) (n j) k) →
      (∀ j ∈ jobs, CyclicFactorSeedInput p l s t u solveTarget (a j) (n j) []
        (embStk (ports.small ∘ factorReg) (F j))) →
      (∀ j ∈ jobs, (H j).span+(K j).span = n j) →
      (jobs.map (fun j => (H j).span+(K j).span+1)).sum ≤ volume →
      (∀ j ∈ jobs, steps j ≤ readSupplierEndpointsCost V (a j) (n j)+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost (H j) (K j) W N (S j)+
            (ports.factorTimeCost s t p u (a j) (n j) (C j) (F j)+
              ((4*(W+radius j+core j)+13)+numerical j))) (N*n j*W)+(2*(a j+(a j+n j))+5)) →
      (jobs.map steps).sum ≤ b*(jobs.map numerical).sum+(3*b+1)*Sizes.T m+(b*D+8*cW)*N*volume*p := by
  dsimp only
  let b := 8*executionPush (A := A) (U := U) hR hQ+1
  let D := 32*cW+2*(4*cW+12*cw+28)+70
  filter_upwards [selectedFittingCyclicInputScheduleTime_le (T := T) (A := A) cw cW,
    selectedCyclicFactorPreparationScheduleTime_le (T := T) (A := A) ct 1,
    selectedCyclicOriginControlScheduleTime_le cV cW 1,
    selectedDistinctCoreSetup_volume_le (4*909+5) 0 0 1] with m hinput hfactor hcontrol hfixed
  intro ι h i _ jobs ports H K S C F u target V W N volume a n radius core numerical steps
    hcount hu htarget hb hV hW hgeometry hparams hN hheaders hvalues hseed hspans hvolume hsteps
  have hi := hinput h i jobs ports H K S W N volume hcount hW hparams hN hheaders hvolume
  have hf := hfactor h i jobs ports C F u target a n hcount hu htarget hb
    (by intro j hj; exact ⟨(hgeometry j hj).1,(hgeometry j hj).2.1⟩) hvalues hseed
  have hc := hcontrol h i jobs V W a n radius core hcount hV hW hgeometry
  have hconstant := hfixed i jobs (fun _ => 4*909+5) hcount (by intro j hj; simp)
  simp only [one_mul] at hf hc hconstant
  have hfixedSum : (4*909+5)*jobs.length ≤ Sizes.T m := by
    simpa [List.map_const',Nat.mul_comm] using hconstant
  have hsum := cyclicOriginScheduleTime_le_components (A := A) (U := U) hR hQ jobs V W N a n radius core
    (fun j => ports.inputTimeCost (H j) (K j) W N (S j))
    (fun j => ports.factorTimeCost (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u (a j) (n j) (C j) (F j))
    numerical steps hsteps
  have hn : (jobs.map n).sum ≤ volume :=
    (List.sum_le_sum (by intro j hj; have := hspans j hj; omega)).trans hvolume
  have hpayload := Nat.mul_le_mul (Nat.mul_le_mul_left (8*N) hW) hn
  change _ ≤ Sizes.T m+D*N*volume*Sizes.p m at hi
  have hinputScaled := Nat.mul_le_mul_left b hi
  have hfactorScaled := Nat.mul_le_mul_left b hf
  have hcontrolScaled := Nat.mul_le_mul_left b hc
  change _ ≤ b*(_+_+_+_)+_+_ at hsum
  change (jobs.map steps).sum ≤ b*(jobs.map numerical).sum+(3*b+1)*Sizes.T m+
    (b*D+8*cW)*N*volume*Sizes.p m
  nlinarith only [hsum,hinputScaled,hfactorScaled,hcontrolScaled,hfixedSum,hpayload]

end IntegerMultBounds.MathlibTM2.Cost
