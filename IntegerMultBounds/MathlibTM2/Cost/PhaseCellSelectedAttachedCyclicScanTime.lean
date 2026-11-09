module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedCyclicScanTime
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

theorem selectedAttachedCyclicScan_time_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
    let b := 8*executionPush (A := A) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m)
      (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u
        (haloInverseRingLog (Sizes.s m i) (Sizes.t m i)) α d,
      ∀ (ports : CyclicComplexCallerLayout T) (_S₀ : Stacks T A)
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
      ∀ H K : {k // k ∈ jobs} → ReplicaHaloProblem s,
      (∀ c : {k // k ∈ jobs}, ∃ (ha : origin c.val < s) (hn : L ≤ s)
        (Fs : List (ZMod s → GaussianInt)) (hF : ∀ R ∈ Fs, ∀ j, ‖value (q c.val) (R j)‖ ≤ (2 : ℝ)^2),
        Fs.length = 2*count ∧ H c = axis.cyclicLeftReplicaProblem (stage c.val) 2 (origin c.val) L ha Fs hF ∧
          K c = axis.cyclicRightReplicaProblem (stage c.val) 2 (origin c.val) L hn Fs hF) →
      2*p+13 ≤ W → W ≤ cW*p → V ≤ cV*p →
      (∀ c : {k // k ∈ jobs}, ∃ (J M : ReplicaHaloProblem s) (S C F : Stacks T A),
        (∀ j ∈ recoverySeedHeaderPorts, (S.R (ports.seedL j)).length = recoverySeedHeader (H c) W count j) ∧
        (∀ j ∈ recoverySeedHeaderPorts, (S.R (ports.seedR j)).length = recoverySeedHeader (K c) W count j) ∧
        CyclicFactorSeedInput p l s t u solveTarget (origin c.val) L []
          (embStk (ports.small ∘ factorReg) F) ∧
        (∀ j, (C.R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span j)).length =
          cyclicFactorMasterValues p l s t u solveTarget (origin c.val) L j) ∧
        CyclicSecondInteriorProfile (H c) (K c) J M p solveTarget (N c.val)) →
      B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p → band ≤ cZ*p →
      let time := fun c : {k // k ∈ jobs} => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H c) (K c)
        p u l t (origin c.val) L target (q c.val) W (depth*band) (coreLength s width c.val) (2*count) count V
      ∀ steps : ℕ, steps ≤ (jobs.attach.map time).sum+5*jobs.length+4 →
      (steps : ℝ) ≤ (8*(b : ℝ)+3)*(Sizes.T m : ℝ)+B₀*(2*(count : ℝ)+1)*
        ((t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) := by
  classical
  dsimp only
  obtain ⟨B₀,hB₀,hbase⟩ := selectedGeneratedCyclicScan_time_le (T := T) (A := A) (U := U)
    hR hQ ct cW cV cZ hcZ
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hbase,selectedAxisPolynomial_le_volume 4 0 0] with m hbase hunit
  intro h i _ u α d axis ports S₀ width depth L count target W V B hu htarget
    hw hwidth hguard hcell hprepare H K hactual hW hWmax hV hcert hB hl htargetMax hband steps hsteps
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
  let time := fun c : {k // k ∈ jobs} => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H c) (K c)
    p u l t (origin c.val) L target (q c.val) W (depth*band) (coreLength s width c.val) (2*count) count V
  by_cases hnil : jobs = []
  · change steps ≤ (jobs.attach.map time).sum+5*jobs.length+4 at hsteps
    have hempty : jobs.attach = [] := List.eq_nil_of_length_eq_zero (by simp [hnil])
    simp only [hempty,List.map_nil,List.sum_nil,hnil,List.length_nil,Nat.mul_zero,Nat.zero_add] at hsteps
    have hT := hunit i
    simp only [pow_zero,Nat.mul_one] at hT
    have hsR : (steps : ℝ) ≤ 4 := by exact_mod_cast hsteps
    have hTR : (4 : ℝ) ≤ Sizes.T m := by exact_mod_cast hT
    have htNonneg : (0 : ℝ) ≤ Sizes.T m := Nat.cast_nonneg _
    have hnum : 0 ≤ B₀*(2*(count : ℝ)+1)*
        ((t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) := by positivity
    have hb : (0 : ℝ) ≤ 8*executionPush (A := A) (U := U) hR hQ+1 := by positivity
    nlinarith only [hsR,hTR,htNonneg,hnum,hb]
  · obtain ⟨k₀,hk₀⟩ := List.exists_mem_of_ne_nil jobs hnil
    let Htotal := fun k => if hk : k ∈ jobs then H ⟨k,hk⟩ else H ⟨k₀,hk₀⟩
    let Ktotal := fun k => if hk : k ∈ jobs then K ⟨k,hk⟩ else K ⟨k₀,hk₀⟩
    let totalTime := fun k => generatedOriginTimeCost (A := A) (U := U) hR hQ B (Htotal k) (Ktotal k)
      p u l t (origin k) L target (q k) W (depth*band) (coreLength s width k) (2*count) count V
    have hmap : jobs.attach.map time = jobs.map totalTime := by
      rw [← List.attach_map_val (l := jobs) (f := totalTime)]
      apply List.map_congr_left
      intro c hc
      simp only [time,totalTime,Htotal,Ktotal,dite_eq_left c.property]
      cases c; rfl
    apply hbase h i axis ports S₀ width depth L count target W V B hu htarget
      hw hwidth hguard hcell hprepare Htotal Ktotal
      (by
        intro k hk
        change k ∈ jobs at hk
        simpa only [Htotal,Ktotal,dite_eq_left hk] using hactual ⟨k,hk⟩)
      hW hWmax hV
      (by
        intro k hk
        change k ∈ jobs at hk
        simpa only [Htotal,Ktotal,dite_eq_left hk] using hcert ⟨k,hk⟩)
      hB hl htargetMax hband steps
    change steps ≤ (jobs.attach.map time).sum+5*jobs.length+4 at hsteps
    change steps ≤ (jobs.map totalTime).sum+5*jobs.length+4
    rwa [hmap] at hsteps

end IntegerMultBounds.MathlibTM2.Cost
