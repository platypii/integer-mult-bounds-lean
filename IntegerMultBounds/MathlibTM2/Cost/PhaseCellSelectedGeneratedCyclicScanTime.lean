module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedOriginClassTime
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

theorem selectedGeneratedCyclicScan_time_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
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
      ∀ H K : ℕ → ReplicaHaloProblem s,
      (∀ k ∈ jobs, ∃ (ha : origin k < s) (hn : L ≤ s)
        (Fs : List (ZMod s → GaussianInt)) (hF : ∀ R ∈ Fs, ∀ j, ‖value (q k) (R j)‖ ≤ (2 : ℝ)^2),
        Fs.length = 2*count ∧ H k = axis.cyclicLeftReplicaProblem (stage k) 2 (origin k) L ha Fs hF ∧
          K k = axis.cyclicRightReplicaProblem (stage k) 2 (origin k) L hn Fs hF) →
      2*p+13 ≤ W → W ≤ cW*p → V ≤ cV*p →
      (∀ k ∈ jobs, ∃ (J M : ReplicaHaloProblem s) (S C F : Stacks T A),
        (∀ j ∈ recoverySeedHeaderPorts, (S.R (ports.seedL j)).length = recoverySeedHeader (H k) W count j) ∧
        (∀ j ∈ recoverySeedHeaderPorts, (S.R (ports.seedR j)).length = recoverySeedHeader (K k) W count j) ∧
        CyclicFactorSeedInput p l s t u solveTarget (origin k) L []
          (embStk (ports.small ∘ factorReg) F) ∧
        (∀ j, (C.R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span j)).length =
          cyclicFactorMasterValues p l s t u solveTarget (origin k) L j) ∧
        CyclicSecondInteriorProfile (H k) (K k) J M p solveTarget (N k)) →
      B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p → band ≤ cZ*p →
      let time := fun k => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H k) (K k)
        p u l t (origin k) L target (q k) W (depth*band) (coreLength s width k) (2*count) count V
      ∀ steps : ℕ, steps ≤ (jobs.map time).sum+5*jobs.length+4 →
      (steps : ℝ) ≤ (8*(b : ℝ)+3)*(Sizes.T m : ℝ)+B₀*(2*(count : ℝ)+1)*
        ((t : ℝ)*(1+(band : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) := by
  classical
  dsimp only
  obtain ⟨B₀,hB₀,hclass⟩ := selectedGeneratedOriginCyclicClass_time_le (T := T) (A := A) (U := U)
    hR hQ ct cW cV cZ hcZ
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hclass,selectedAxisPolynomial_le_volume 14 0 1] with m hclass hloop
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
  let time := fun k => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H k) (K k)
    p u l t (origin k) L target (q k) W (depth*band) (coreLength s width k) (2*count) count V
  choose J M S C F hdata using hcert
  let Jall := fun k => if hk : k ∈ jobs then J k hk else H k
  let Mall := fun k => if hk : k ∈ jobs then M k hk else K k
  let Sall := fun k => if hk : k ∈ jobs then S k hk else S₀
  let Call := fun k => if hk : k ∈ jobs then C k hk else S₀
  let Fall := fun k => if hk : k ∈ jobs then F k hk else S₀
  have hbound := hclass h i axis ports Sall Call Fall width depth L count target W V B hu htarget
    hw hwidth hguard hcell hprepare H K Jall Mall hactual
    (by intro k hk; change k ∈ jobs at hk; simpa only [Jall,Mall,dite_eq_left hk] using (hdata k hk).2.2.2.2)
    hW hWmax hV
    (by intro k hk; change k ∈ jobs at hk; simpa only [Sall,dite_eq_left hk] using ⟨(hdata k hk).1,(hdata k hk).2.1⟩)
    (by intro k hk; change k ∈ jobs at hk; simpa only [Call,dite_eq_left hk] using (hdata k hk).2.2.2.1)
    (by intro k hk; change k ∈ jobs at hk; simpa only [Fall,dite_eq_left hk] using (hdata k hk).2.2.1)
    hB hl htargetMax hband time (by intro k hk; exact le_rfl)
  have hcountJobs : jobs.length ≤ 2*t := by
    have hc := coreGatherIndices_length_le s width (depth*band) L hw
    have ht : s < t := h.good.lt i
    change (coreGatherIndices s width (depth*band) L).length ≤ 2*t
    omega
  have hcounter : 5*jobs.length+4 ≤ Sizes.T m := by
    have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
    have hv := hloop i
    simp only [pow_one,pow_zero,Nat.mul_one] at hv
    change 14*t ≤ Sizes.T m at hv
    omega
  have hsR := (Nat.cast_le (α := ℝ)).mpr hsteps
  have hcR := (Nat.cast_le (α := ℝ)).mpr hcounter
  change (steps : ℝ) ≤ ((jobs.map time).sum+5*jobs.length+4 : ℕ) at hsR
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hsR hcR
  change ((jobs.map time).sum : ℝ) ≤ _ at hbound
  linarith only [hsR,hcR,hbound]

end IntegerMultBounds.MathlibTM2.Cost
