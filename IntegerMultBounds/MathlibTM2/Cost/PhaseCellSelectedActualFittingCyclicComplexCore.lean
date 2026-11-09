module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedActualFittingCyclicCaller
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicSecondInteriorBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicPostprocess
import Mathlib.Tactic.Linarith

/-! Compose every term of the executed fitting complex-core time allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

noncomputable def cyclicComplexCoreTimeCost {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (p u l t a span target q W radius core replicas fields : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (cyclicPrincipalBoundary s t band a span).card
  let solveTarget := boundaryRecoveryTarget p (target+1)
  (cachedCyclicReplicaBoundaryBill H K p u l t a span solveTarget q (2*q+8) N (24*band+1) replicas+
    solvedCyclicRecoveryCost H K replicas N span (2*q+8))+
  cyclicSecondInteriorTimeBudget H K p solveTarget N+
  cyclicPostprocessTimeCost p q W s a span H.span K.span radius core replicas fields

/-- Identify the composed counter with the term order of the executed complex
core endpoint. This is a symbolic ledger equality, independent of tape data. -/
theorem cyclicComplexCoreTimeCost_eq_components {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (p u l t a span target q W radius core replicas fields : ℕ)
    (hwH : H.wordWidth = 2*q+8) (hwK : K.wordWidth = 2*q+8)
    (hhalo : span = core+2*radius) :
    let band := PhaseCellBand.width p u
    let N := (cyclicPrincipalBoundary s t band a span).card
    let solveTarget := boundaryRecoveryTarget p (target+1)
    cyclicComplexCoreTimeCost H K p u l t a span target q W radius core replicas fields =
    cachedCyclicReplicaBoundaryBill H K p u l t a span solveTarget q (2*q+8) N (24*band+1) replicas+
      solvedCyclicRecoveryCost H K replicas N span (2*q+8)+
      cyclicSecondInteriorTimeBudget H K p solveTarget N+
      ((replicas*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
        (replicas*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4))+
      (PackedRecoveryNormalization.normalizationCost p q W a (min span (s-a)) replicas+
        PackedRecoveryNormalization.normalizationCost p q W 0 (span-min span (s-a)) replicas)+
      (packedCoreArchiveControlsCost radius core W replicas+
        (replicas*(packedCoreArchiveStepCost radius core (core+2*radius) W+3)+2)+
        (2*(radius*W+core*W+(core+2*radius))+7))+
      ((6*fields+4)+((core*(4*W+9)+4)+(fields*(16*(core*W)+9)+14)+(2*(core*W)+2))+
        (2*fields+2)) := by
  dsimp only [cyclicComplexCoreTimeCost,cyclicPostprocessTimeCost,cyclicPublicationTrafficCost]
  rw [hwH,hwK,hhalo]
  ring

private theorem sum_three {ι : Type} (jobs : List ι) (f g h : ι → ℕ) :
    (jobs.map (fun k => f k+g k+h k)).sum =
      (jobs.map f).sum+(jobs.map g).sum+(jobs.map h).sum := by
  induction jobs with
  | nil => simp
  | cons k jobs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem selectedActualFittingCyclicComplexCore_time_le (ct cW : ℕ) :
    let cw := 1032+8*ct
    ∃ E C F : ℝ, 0 ≤ E ∧ 0 ≤ C ∧ 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s n i) (Sizes.t n i) (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) α d,
      ∀ width depth L replicas target W : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      let p := Sizes.p n
      let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
      let band := PhaseCellBand.width p u
      let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
      let origin := fun k => coreStart width k-depth*band
      let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band (origin k) L).card
      let stage := fun k => initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (N k)) 2
      let q := fun k => executionPrecision p l (stage k) 2
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K J M : ℕ → ReplicaHaloProblem (Sizes.s n i),
      (∀ k ∈ jobs, ∃ (ha : origin k < Sizes.s n i) (hn : L ≤ Sizes.s n i)
        (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
        (hF : ∀ F ∈ Fs, ∀ j, ‖value (q k) (F j)‖ ≤ (2 : ℝ)^2),
        Fs.length = replicas ∧
        H k = axis.cyclicLeftReplicaProblem (stage k) 2 (origin k) L ha Fs hF ∧
        K k = axis.cyclicRightReplicaProblem (stage k) 2 (origin k) L hn Fs hF) →
      (∀ k ∈ jobs, CyclicSecondInteriorProfile (H k) (K k) (J k) (M k) p
        (boundaryRecoveryTarget p (target+1)) (N k)) →
      2*p+13 ≤ W → W ≤ cW*p → ∀ fields : ℕ → ℕ,
      (∀ k ∈ jobs, fields k ≤ replicas) →
      ((jobs.map (fun k => cyclicComplexCoreTimeCost (H k) (K k) p u l (Sizes.t n i)
        (origin k) L target (q k) W (depth*band) (coreLength (Sizes.s n i) width k)
        replicas (fields k))).sum : ℝ) ≤
      5*(Sizes.T n : ℝ)+
      4200*replicas*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      2800*(replicas+1)*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      800*((30*cw+50 : ℕ)*(replicas+1)*(Sizes.p n : ℝ)+
        replicas*C*(Sizes.p n : ℝ)^(129/128 : ℝ))*
          ((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)+
      680*(E+F)*replicas*((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ)+
      7600*(replicas+1)*(Sizes.s n i : ℝ)*(cw*Sizes.p n+W+1 : ℕ) := by
  dsimp only
  let cw := 1032+8*ct
  let cV := (2*(16*20+8*cw+8*2+128)+426009)*cw
  obtain ⟨E,C,hE,hC,hcaller⟩ := selectedActualFittingCyclicCaller_time_le ct
  obtain ⟨F,hF,hsecond⟩ := selectedFittingCyclicSecondInteriorBudget_time_le 20 cw 20 cV
  refine ⟨E,C,F,hE,hC,hF,?_⟩
  filter_upwards [hcaller,hsecond,selectedFittingCyclicPostprocess_time_le cw cW] with n hc hs hp
  intro h i _ u α d axis width depth L replicas target W hu htarget
  intro hw hwidth hguard hcell hprepare H K J M hactual hprofile hW hWbound fields hfields
  let p := Sizes.p n
  let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
  let band := PhaseCellBand.width p u
  let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
  let origin := fun k => coreStart width k-depth*band
  let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band (origin k) L).card
  let stage := fun k => initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (N k)) 2
  let q := fun k => executionPrecision p l (stage k) 2
  have heq (k : ℕ) : executionWidth p l (stage k) 2 = 2*q k+8 := by
    dsimp only [q]
    unfold executionWidth executionPrecision
    omega
  have hq : ∀ k ∈ jobs, 2*q k+8 ≤ cw*p := by
    intro k hk
    have hh := selectedCyclicWorkingWidth_le ct h i u target (origin k) L htarget axis.hband
    change executionWidth p l (stage k) 2 ≤ cw*p at hh
    rwa [heq k] at hh
  have hgeom : ∀ k ∈ jobs, (H k).p = p ∧ (H k).t = Sizes.t n i ∧ (H k).band = band ∧
      (H k).origin = origin k ∧ (H k).span = min L (Sizes.s n i-origin k) ∧
      (K k).p = p ∧ (K k).t = Sizes.t n i ∧ (K k).band = band ∧
      (K k).span = L-min L (Sizes.s n i-origin k) := by
    intro k hk
    obtain ⟨ha,hn,Fs,hFs,hlen,hH,hK⟩ := hactual k hk
    rw [hH,hK]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have hparams : ∀ k ∈ jobs, ∀ R ∈ [H k,K k],
      R.Fs.length = replicas ∧ R.u ≤ R.p ∧ R.l ≤ 20*R.p ∧ R.wordWidth ≤ cw*R.p ∧
      2^R.l ≤ 20*R.p ∧ R.metadataWidth ≤ cV*R.p ∧ R.l = haloInverseRingLog (Sizes.s n i) R.t := by
    intro k hk R hR
    obtain ⟨ha,hn,Fs,hFs,hlen,hH,hK⟩ := hactual k hk
    have hprof := selectedCyclicReplicaProblems_profile ct h i axis target (origin k) L ha hn hu htarget Fs hFs
    rw [hH,hK] at hR
    obtain ⟨hpR,htR,hlR,huR,_,_,hFsR,hwR,_,hVR,hl,hr⟩ := hprof R hR
    refine ⟨by rw [hFsR]; exact hlen,by rw [huR,hpR]; exact hu,hl,?_,hr,?_,?_⟩
    · rw [hwR,hpR]
      change executionWidth p l (stage k) 2 ≤ cw*p
      rw [heq k]
      exact hq k hk
    · simpa only [hpR] using hVR
    · rw [hlR,htR]
  have hc' := hc h i axis width depth L replicas target hu htarget hw hwidth hguard hcell hprepare H K hactual
  have hs' := hs h i width band depth L replicas hw hwidth hguard (PhaseCellBand.width_pos p u)
    hcell hprepare H K J M hgeom (by intro k hk; exact ⟨(hprofile k hk).leftLayout,(hprofile k hk).rightLayout⟩)
    hparams (fun _ => boundaryRecoveryTarget p (target+1)) N (by
      intro k hk
      exact ⟨(hprofile k hk).leftTarget,(hprofile k hk).rightTarget,
        (hprofile k hk).leftExponent,(hprofile k hk).rightExponent⟩)
  have hp' := hp h i width (depth*band) L replicas W hw hwidth hguard hW hWbound
    q (fun k => (H k).span) (fun k => (K k).span) fields (by
      intro k hk
      obtain ⟨_,_,_,_,hspanH,_,_,_,hspanK⟩ := hgeom k hk
      exact ⟨hq k hk,by rw [hspanH,hspanK]; omega,hfields k hk⟩)
  have he := sum_three jobs
    (fun k => cachedCyclicReplicaBoundaryBill (H k) (K k) p u l (Sizes.t n i) (origin k) L
      (boundaryRecoveryTarget p (target+1)) (q k) (2*q k+8) (N k) (24*band+1) replicas+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))
    (fun k => cyclicSecondInteriorTimeBudget (H k) (K k) p (boundaryRecoveryTarget p (target+1)) (N k))
    (fun k => cyclicPostprocessTimeCost p (q k) W (Sizes.s n i) (origin k) L
      (H k).span (K k).span (depth*band) (coreLength (Sizes.s n i) width k) replicas (fields k))
  have hpR := (Nat.cast_le (α := ℝ)).mpr hp'
  dsimp only [jobs,origin,N,q,stage,p,l,band] at he
  dsimp only at hc' hs'
  dsimp only [cyclicComplexCoreTimeCost]
  have heR := congrArg (fun x : ℕ => (x : ℝ)) he
  dsimp only [jobs,origin,N,q,stage,p,l,band,cw] at heR hc' hs' hpR ⊢
  push_cast at heR hc' hs' hpR ⊢
  nlinarith only [heR,hc',hs',hpR]

end IntegerMultBounds.MathlibTM2.Cost
