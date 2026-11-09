module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicCallerSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicPreparedScheduleFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicCallerSharedSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFactorySchedule
import Mathlib.Tactic.Linarith

/-! Selected time estimate for the actual fitting cyclic boundary caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_pair {ι : Type} (jobs : List ι) (f g : ι → ℕ) :
    (jobs.map (fun j => f j+g j)).sum = (jobs.map f).sum+(jobs.map g).sum := by
  induction jobs with
  | nil => simp
  | cons j jobs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem selectedFittingCyclicCaller_time_le (ct ce cw cV cl cr : ℕ) :
    ∃ E C : ℝ, 0 ≤ E ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (width band depth L replicas u target : ℕ),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → band = PhaseCellBand.width (Sizes.p n) u →
      band ≤ Sizes.s n i →
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width → 1 ≤ band →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width →
      (Sizes.p n)^2+band^2 ≤ width →
      ∀ H K : ℕ → ReplicaHaloProblem (Sizes.s n i),
      ∀ q : ℕ → ℕ,
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        (H k).p = Sizes.p n ∧ (H k).t = Sizes.t n i ∧ (H k).band = band ∧
        (H k).origin = coreStart width k-depth*band ∧
        (H k).span = min L (Sizes.s n i-(coreStart width k-depth*band)) ∧
        (K k).p = Sizes.p n ∧ (K k).t = Sizes.t n i ∧ (K k).band = band ∧
        (K k).span = L-min L (Sizes.s n i-(coreStart width k-depth*band))) →
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        (H k).l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (K k).l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (H k).u ≤ Sizes.p n ∧ (K k).u ≤ Sizes.p n ∧
        (H k).target ≤ ct*Sizes.p n ∧ (K k).target ≤ ct*Sizes.p n ∧
        (H k).rhsExp ≤ ce*Sizes.p n ∧ (K k).rhsExp ≤ ce*Sizes.p n ∧
        (H k).Fs.length = replicas ∧ (K k).Fs.length = replicas ∧
        (H k).wordWidth = (2*q k+8) ∧ (K k).wordWidth = (2*q k+8) ∧
        (2*q k+8) ≤ cw*Sizes.p n ∧ (H k).metadataWidth ≤ cV*Sizes.p n ∧
        (K k).metadataWidth ≤ cV*Sizes.p n) →
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        ∀ R ∈ [H k,K k], R.l ≤ cl*R.p ∧ 2^R.l ≤ cr*R.p) →
      let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
      let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band
        (coreStart width k-depth*band) L).card
      ((jobs.map (fun k => cachedCyclicReplicaBoundaryBill (H k) (K k) (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i)
        (coreStart width k-depth*band) L (boundaryRecoveryTarget (Sizes.p n) (target+1))
        (q k) (2*q k+8) (N k) (24*band+1) replicas+
        solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))).sum : ℝ) ≤
      2*(Sizes.T n : ℝ)+
      4200*replicas*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      2800*(replicas+1)*(Sizes.s n i : ℝ)*(cw*Sizes.p n+1 : ℕ)+
      800*((30*cw+50 : ℕ)*(replicas+1)*(Sizes.p n : ℝ)+
        replicas*C*(Sizes.p n : ℝ)^(129/128 : ℝ))*
          ((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)+
      680*E*replicas*((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨E,hE,hpass⟩ := computedFittingCyclicPassSchedule_fast_le ct ce cw cV
  obtain ⟨C,hC,hbatch⟩ := computedFittingCyclicPreparedSchedule_fast_le cw
  refine ⟨E,C,hE,hC,?_⟩
  filter_upwards [selectedCyclicCallerSharedSchedule_volume_le cl cw cr cV 1,
    selectedCyclicCoreClassFactory_volume_le ct 1] with n hshared hfactory
  intro h i _ width band depth L replicas u target hu htarget hbandEq hbandFit
    hw hwidth hguard hband hcell hprepare H K q hgeom hparams hsetup
  let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
  let N := fun k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band
    (coreStart width k-depth*band) L).card
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hq : ∀ k ∈ jobs, 2*q k+8 ≤ cw*Sizes.p n := by
    intro k hk
    exact (hparams k hk).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcount : jobs.length ≤ 2*Sizes.t n i := by
    have hc := coreGatherIndices_length_le (Sizes.s n i) width (depth*band) L hw
    have hh := h.good.lt i
    dsimp only [jobs]
    omega
  have hs := hshared h i jobs H K hcount (by
    intro k hk R hR
    obtain ⟨hpH,htH,_,_,_,hpK,htK,_,_⟩ := hgeom k hk
    obtain ⟨_,_,huH,huK,_,_,_,_,_,_,hwH,hwK,hw',hVH,hVK⟩ := hparams k hk
    obtain ⟨hl,hr⟩ := hsetup k hk R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨hpH,htH,by simpa only [hpH] using huH,hl,
        by simpa only [hwH,hpH] using hw',hr,by simpa only [hpH] using hVH⟩
    · exact ⟨hpK,htK,by simpa only [hpK] using huK,hl,
        by simpa only [hwK,hpK] using hw',hr,by simpa only [hpK] using hVK⟩)
  simp only [one_mul] at hs
  have hf := hfactory h i u target width (depth*band) L hu htarget (by simpa only [←hbandEq] using hbandFit) hw
  simp only [one_mul] at hf
  have hb := hbatch (h.good.lt i) (Sizes.p n) width band depth L replicas hp hw hwidth
    hguard hband (by omega) q hq
  have ht := computedFittingCyclicTraffic_sum_le (Sizes.s n i) width (depth*band) L
    (Sizes.p n) cw hw hwidth hguard N (fun k => 2*q k+8) (by
      intro k hk
      obtain ⟨hl,hr,hL⟩ := coreGatherIndices_spec (Sizes.s n i) width (depth*band) L k hk
      have hstart := coreIndex_start_lt (Sizes.s n i) width k hw (List.mem_filter.mp hk).1
      have ha : coreStart width k-depth*band < Sizes.s n i := by omega
      have hn : L ≤ Sizes.s n i := by omega
      exact ⟨(cyclicPrincipalBoundary_card (Sizes.t n i) band _ L (h.good.lt i) ha hn).trans
        (Nat.min_le_left _ _),hq k hk⟩)
  have hpa := hpass h i width band depth L replicas hw hwidth hguard hband hcell hprepare
    H K N (fun k => 2*q k+8) hgeom hparams
  have hl := computedFittingCyclicCaller_schedule_le (h.good.lt i) (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) width depth L
    (boundaryRecoveryTarget (Sizes.p n) (target+1)) replicas cw hw hwidth
    (by simpa only [←hbandEq] using hguard) H K q (by
      intro k hk
      have hk' : k ∈ jobs := by simpa only [←hbandEq] using hk
      obtain ⟨_,_,_,_,hsH,_,_,_,hsK⟩ := hgeom k hk'
      obtain ⟨_,_,_,_,_,_,_,_,hH,hK,hwH,hwK,_,_,_⟩ := hparams k hk'
      exact ⟨hH,hK,hwH,hwK,by rw [hsH,hsK]; omega,hq k hk'⟩)
  have hsR := (Nat.cast_le (α := ℝ)).mpr hs
  have hfR := (Nat.cast_le (α := ℝ)).mpr hf
  have htR := (Nat.cast_le (α := ℝ)).mpr ht
  have hlR := (Nat.cast_le (α := ℝ)).mpr hl
  rw [sum_pair] at hsR
  dsimp only [jobs,N] at hsR htR hpa hlR
  simp only [←hbandEq] at hfR hlR
  dsimp only
  push_cast at hsR hfR htR hlR hb hpa ⊢
  nlinarith only [hsR,hfR,htR,hlR,hb,hpa,
    mul_le_mul_of_nonneg_left htR (by positivity : (0 : ℝ) ≤ 300*replicas)]

end IntegerMultBounds.MathlibTM2.Cost
