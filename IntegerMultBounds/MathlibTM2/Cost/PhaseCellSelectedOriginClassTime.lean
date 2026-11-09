module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicOriginScheduleTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicOriginFastEnvelope
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedActualFittingCyclicComplexCore

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

theorem selectedOriginCyclicClass_time_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (ct cW cV : ℕ) :
    let b := 8*executionPush (A := A) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m)
      (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u
        (haloInverseRingLog (Sizes.s m i) (Sizes.t m i)) α d,
      ∀ (ports : CyclicComplexCallerLayout T) (S C F : ℕ → Stacks T A)
        (width depth L count target W V : ℕ), u ≤ Sizes.p m → target ≤ ct*Sizes.p m →
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
      let numerical := fun k => cyclicComplexCoreTimeCost (H k) (K k) p u l t (origin k) L target (q k) W
        (depth*band) (coreLength s width k) (2*count) count
      ∀ steps : ℕ → ℕ,
      (∀ k ∈ jobs, steps k ≤ readSupplierEndpointsCost V (origin k) L+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost (H k) (K k) W count (S k)+
            (ports.factorTimeCost s t p u (origin k) L (C k) (F k)+
              ((4*(W+depth*band+coreLength s width k)+13)+numerical k))) (count*L*W)+
          (2*(origin k+(origin k+L))+5)) →
      ((jobs.map steps).sum : ℝ) ≤ (8*(b : ℝ)+1)*(Sizes.T m : ℝ)+B₀*(2*(count : ℝ)+1)*
        ((t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  let b := 8*executionPush (A := A) (U := U) hR hQ+1
  let cw := 1032+8*ct
  let D := 32*cW+2*(4*cW+12*cw+28)+70
  let E := b*D+8*cW
  obtain ⟨A₀,hA₀,hnumeric⟩ := selectedActualFittingCyclicComplexCore_time_le ct cW
  refine ⟨(b : ℝ)*A₀+7*E,by positivity,?_⟩
  filter_upwards [hnumeric,selectedCyclicOriginScheduleTime_le (T := T) (A := A) (U := U) hR hQ ct cw cW cV] with m hnum hoverhead
  intro h i _ u α d axis ports S C F width depth L count target W V hu htarget
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
  intro steps hsteps
  have hfamily := selectedCyclicReplicaFamily_profile ct h i axis jobs target (2*count) origin (fun _ => L)
    H K hu htarget hactual
  have hgeometry : ∀ k ∈ jobs, origin k ≤ s ∧ L ≤ s ∧ depth*band+coreLength s width k ≤ s := by
    intro k hk
    obtain ⟨ha,hn,Fs,hFs,_,_,_⟩ := hactual k hk
    have hg := coreGatherIndices_spec s width (depth*band) L k hk
    exact ⟨ha.le,hn,by omega⟩
  have hcountJobs : jobs.length ≤ 2*t := by
    have hc := coreGatherIndices_length_le s width (depth*band) L hw
    have ht : s < t := h.good.lt i
    change (coreGatherIndices s width (depth*band) L).length ≤ 2*t
    omega
  have hvolume := fittingCyclicInputCoordinates_sum_le width (depth*band) L H K hw hwidth hguard
    (by intro k hk; exact (hfamily k hk).2.2.le)
  have ho := hoverhead h i jobs ports H K S C F u target V W count (7*s) origin (fun _ => L)
    (fun _ => depth*band) (fun k => coreLength s width k) numerical steps hcountJobs hu htarget axis.hband hV hWmax
    hgeometry (fun k hk => (hfamily k hk).1) (fun k hk => (hfamily k hk).2.1)
    hheaders hvalues hseed (fun k hk => (hfamily k hk).2.2) hvolume hsteps
  have hn := hnum h i axis width depth L (2*count) target W hu htarget hw hwidth hguard hcell hprepare
    H K J M hactual hprofile hW hWmax (fun _ => count) (by intro k hk; omega) numerical (by intro k hk; exact le_rfl)
  change (jobs.map steps).sum ≤ b*(jobs.map numerical).sum+(3*b+1)*Sizes.T m+E*count*(7*s)*p at ho
  have hoR := (Nat.cast_le (α := ℝ)).mpr ho
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hoR hn
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by have := h.thirteen_le_p; dsimp only [p]; omega)
  have hpower := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast (h.good.lt i).le
  have hdensity : (s : ℝ) ≤ (t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)) := by
    have hnonneg := mul_nonneg (Nat.cast_nonneg t)
      (div_nonneg (sq_nonneg (band : ℝ)) (Nat.cast_nonneg (Sizes.d m)))
    nlinarith only [hstR,hnonneg]
  exact cyclicOriginTime_fast_envelope _ _ (b : ℝ) (E : ℝ) A₀ _ (count : ℝ) (s : ℝ) (p : ℝ) _ _
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hdensity hpower hoR hn

end IntegerMultBounds.MathlibTM2.Cost
