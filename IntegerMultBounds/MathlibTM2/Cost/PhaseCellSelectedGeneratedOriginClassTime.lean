module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedOriginClassTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicSeedCosts
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedOriginTimeCost

/-! Complete fast-time accounting for the ordinary fitting origin class.
Actual cyclic problems discharge every numerical input profile. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  CyclicComplexCallerLayout
open CyclicReplicaPlacement
variable {T Q A : ℕ} {U : Type}

theorem selectedGeneratedOriginCyclicClass_time_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
    let b := 8*executionPush (A := A) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m)
      (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u
        (haloInverseRingLog (Sizes.s m i) (Sizes.t m i)) α d,
      ∀ (ports : CyclicComplexCallerLayout T) (S C F : ℕ → Stacks T A)
        (width depth L count target W V B : ℕ), u ≤ Sizes.p m → target ≤ ct*Sizes.p m →
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let jobs := coreGatherIndices s width (depth*band) L
      let origin := fun k => coreStart width k-depth*band
      let N := fun k => (cyclicPrincipalBoundary s t band (origin k) L).card
      let solveTarget := boundaryRecoveryTarget p (target+1)
      let stage := fun k => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (N k)) 2
      let q := fun k => executionPrecision p l (stage k) 2
      0 < width → width ≤ s → depth*band ≤ width → s/(t-s)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K J M : ℕ → ReplicaHaloProblem s,
      (∀ k ∈ jobs, ∃ (ha : origin k < s) (hn : L ≤ s)
        (Fs : List (ZMod s → GaussianInt)) (hF : ∀ R ∈ Fs, ∀ j, ‖value (q k) (R j)‖ ≤ (2 : ℝ)^2),
        Fs.length = 2*count ∧ H k = axis.cyclicLeftReplicaProblem (stage k) 2 (origin k) L ha Fs hF ∧
          K k = axis.cyclicRightReplicaProblem (stage k) 2 (origin k) L hn Fs hF) →
      (∀ k ∈ jobs, CyclicSecondInteriorProfile (H k) (K k) (J k) (M k) p solveTarget (N k)) →
      2*p+13 ≤ W → W ≤ cW*p → V ≤ cV*p →
      (∀ k ∈ jobs,
        (∀ j ∈ recoverySeedHeaderPorts, ((S k).R (ports.seedL j)).length = recoverySeedHeader (H k) W count j) ∧
        (∀ j ∈ recoverySeedHeaderPorts, ((S k).R (ports.seedR j)).length = recoverySeedHeader (K k) W count j)) →
      (∀ k ∈ jobs, ∀ j, ((C k).R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span j)).length =
        cyclicFactorMasterValues p l s t u solveTarget (origin k) L j) →
      (∀ k ∈ jobs, CyclicFactorSeedInput p l s t u solveTarget (origin k) L []
        (embStk (ports.small ∘ factorReg) (F k))) →
      B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p → band ≤ cZ*p →
      ∀ steps : ℕ → ℕ,
      (∀ k ∈ jobs, steps k ≤ generatedOriginTimeCost (A := A) (U := U) hR hQ B (H k) (K k)
        p u l t (origin k) L target (q k) W (depth*band) (coreLength s width k) (2*count) count V) →
      ((jobs.map steps).sum : ℝ) ≤ (8*(b : ℝ)+2)*(Sizes.T m : ℝ)+B₀*(2*(count : ℝ)+1)*
        ((t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  obtain ⟨B₀,hB₀,hbase⟩ := selectedOriginCyclicClass_time_le (T := T) (A := A) (U := U) hR hQ ct cW cV
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hbase,selectedCyclicSeedScheduleTime_le cZ 1 hcZ] with m hbase hsetup
  intro h i _ u α d axis ports S C F width depth L count target W V B hu htarget
  intro hw hwidth hguard hcell hprepare H K J M hactual hprofile hW hWmax hV hheaders hvalues hseed
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let jobs := coreGatherIndices s width (depth*band) L
  let origin := fun k => coreStart width k-depth*band
  let N := fun k => (cyclicPrincipalBoundary s t band (origin k) L).card
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := fun k => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (N k)) 2
  let q := fun k => executionPrecision p l (stage k) 2
  let numerical := fun k => cyclicComplexCoreTimeCost (H k) (K k) p u l t (origin k) L target (q k) W
    (depth*band) (coreLength s width k) (2*count) count
  intro hB hl htargetMax hband steps hsteps
  let base : ℕ → ℕ := fun k =>
    readSupplierEndpointsCost V (origin k) L+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost (H k) (K k) W count (S k)+
            (ports.factorTimeCost s t p u (origin k) L (C k) (F k)+
              ((4*(W+depth*band+coreLength s width k)+13)+numerical k))) (count*L*W)+
          (2*(origin k+(origin k+L))+5)
  let setup : ℕ → ℕ := fun k =>
    CyclicSeedLayout.timeCost B p u l target s t (origin k) L+
        (2*(List.ofFn (inverseMasterValues p u l target s t (origin k) (origin k+L))).sum+21)
  have hbaseTime := hbase h i axis ports S C F width depth L count target W V hu htarget
    hw hwidth hguard hcell hprepare H K J M hactual hprofile hW hWmax hV hheaders hvalues hseed
    base (by intro k hk; exact le_rfl)
  have hcountJobs : jobs.length ≤ 2*t := by
    have hc := coreGatherIndices_length_le s width (depth*band) L hw
    have ht : s < t := h.good.lt i
    change (coreGatherIndices s width (depth*band) L).length ≤ 2*t
    omega
  have hpZ : p ≤ cZ*p := by simpa using Nat.mul_le_mul_right p hcZ
  have hsetupTime := hsetup h i jobs B u l target origin (fun _ => L) hcountJobs hB
    (hu.trans hpZ) hl htargetMax hband (by
      intro k hk
      have hg := coreGatherIndices_spec s width (depth*band) L k hk
      change coreStart width k-depth*band+L ≤ s
      omega)
  change 1*(jobs.map setup).sum ≤ Sizes.T m at hsetupTime
  simp only [one_mul] at hsetupTime
  have hsum : (jobs.map steps).sum ≤ (jobs.map setup).sum+(jobs.map base).sum := by
    rw [← List.sum_map_add]
    apply List.sum_le_sum
    intro k hk
    obtain ⟨ha,hn,Fs,hFs,hcount,hH,hK⟩ := hactual k hk
    have hcountH : (H k).Fs.length = 2*count := by rw [hH]; exact hcount
    have hcountK : (K k).Fs.length = 2*count := by rw [hK]; exact hcount
    have hi := fittingCyclicInputTime_affine ports (H k) (K k) W count (S k)
      hcountH hcountK (hheaders k hk).1 (hheaders k hk).2
    have hf := fittingCyclicFactorTime_eq ports (C k) (F k) p l t u solveTarget (origin k) L
      (hvalues k hk) (hseed k hk)
    have hs := hsteps k hk
    change steps k ≤ generatedOriginTimeCost (A := A) (U := U) hR hQ B (H k) (K k)
      p u l t (origin k) L target (q k) W (depth*band) (coreLength s width k) (2*count) count V at hs
    unfold generatedOriginTimeCost at hs
    change ports.factorTimeCost s t p u (origin k) L (C k) (F k) =
      cyclicFactorTime p l s t u (boundaryRecoveryTarget p (target+1)) (origin k) L at hf
    rw [←hi,←hf] at hs
    dsimp only [setup,base]
    change steps k ≤ readSupplierEndpointsCost V (origin k) L+
      (CyclicSeedLayout.timeCost B p u l target s t (origin k) L+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost (H k) (K k) W count (S k)+
            (ports.factorTimeCost s t p u (origin k) L (C k) (F k)+
              ((4*(W+depth*band+coreLength s width k)+13)+numerical k))) (count*L*W)+
        (2*(List.ofFn (inverseMasterValues p u l target s t (origin k) (origin k+L))).sum+21))+
      (2*(origin k+(origin k+L))+5) at hs
    omega
  have hsumR := (Nat.cast_le (α := ℝ)).mpr hsum
  have hsetupR := (Nat.cast_le (α := ℝ)).mpr hsetupTime
  simp only [Nat.cast_add] at hsumR
  change ((jobs.map base).sum : ℝ) ≤ _ at hbaseTime
  linarith only [hsumR,hsetupR,hbaseTime]

end IntegerMultBounds.MathlibTM2.Cost
