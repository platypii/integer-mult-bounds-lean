module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleLocalLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputSchedule

/-! The complete executed raw-job list has one shared reserve and linear
replica work in the summed interval and sparse numerical volumes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedRawRecoverySchedule_time_le (ct cH cW : ℕ) :
    let cw := 16*20+8*cH+8*2+128
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution)
      (N spanVolume localVolume : ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        r.problem.u ≤ Sizes.p n ∧ r.problem.target ≤ cH*Sizes.p n ∧
        r.problem.rhsExp = 2 ∧ r.problem.Fs.length = N ∧
        1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1 ∧ r.W ≤ cW*Sizes.p n) →
      (records.map (fun r => r.problem.span)).sum ≤ spanVolume →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ localVolume →
      (((records.map (fun r => r.runTime (B r))).sum : ℕ) : ℝ) ≤
        Sizes.T n+(4*cW+12*cw+28 : ℕ)*N*spanVolume*(Sizes.p n : ℝ)+
          F*N*localVolume*(Sizes.p n : ℝ)^(129/128 : ℝ) := by
  dsimp only
  let cw := 16*20+8*cH+8*2+128
  let cV := (2*cw+426009)*cw
  obtain ⟨F,hF,hlocal⟩ := selectedRawRecoverySchedule_local_ledger_le cH 2
  obtain ⟨C,hfactory⟩ := selectedGeneratedReplicaBoundaryFactoryCost_poly_le ct
  refine ⟨F,hF,?_⟩
  filter_upwards [hfactory,selectedDistinctCoreSetup_volume_le C 4 6 3,
    selectedRecoveryInputSharedSchedule_volume_le cw cW 3,
    selectedRawRecoveryCallerSharedSchedule_volume_le 20 cw 20 cV 3] with n hf hsumFactory hinput hcaller
  intro h i _ records B N spanVolume localVolume hcount hparams hspan hvolume
  have hrhs (r) (hr : r ∈ records) : r.problem.rhsExp ≤ 2*Sizes.p n := by
    obtain ⟨_,_,_,_,_,he,_⟩ := hparams r hr
    have := h.thirteen_le_p
    omega
  have hwidths (r) (hr : r ∈ records) :
      r.problem.l ≤ 20*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
      2^r.problem.l ≤ 20*r.problem.p ∧ r.problem.metadataWidth ≤ cV*r.problem.p := by
    obtain ⟨hp,ht,hl,hu,htarget,_,_⟩ := hparams r hr
    obtain ⟨hl',hpow,hw,hV⟩ := selectedHaloGatheredWidths cH 2 h i r.problem.u r.problem.target
      r.problem.rhsExp hu htarget (hrhs r hr)
    have hwH : r.problem.wordWidth ≤ cw*r.problem.p := by
      simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
    have hVw : r.problem.metadataWidth ≤ (2*cw+426009)*r.problem.wordWidth := by
      simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
        ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
    refine ⟨?_,hwH,?_,?_⟩
    · simpa only [hl,hp] using hl'
    · simpa only [hl,hp] using hpow
    · calc
        _ ≤ (2*cw+426009)*r.problem.wordWidth := hVw
        _ ≤ (2*cw+426009)*(cw*r.problem.p) := Nat.mul_le_mul_left _ hwH
        _ = cV*r.problem.p := by dsimp only [cV]; ring
  have hi := hinput i records hcount (by
    intro r hr
    obtain ⟨hp,_,_,_,_,_,_,_,_,hW⟩ := hparams r hr
    exact ⟨hp,by simpa only [hp] using (hwidths r hr).2.1,hW⟩)
  have hc := hcaller h i records B hcount (by
    intro r hr
    obtain ⟨hp,ht,_,hu,_⟩ := hparams r hr
    obtain ⟨hl,hw,hpow,hV⟩ := hwidths r hr
    exact ⟨hp,ht,by simpa only [hp] using hu,hl,hw,hpow,hV⟩)
  have hfac := hsumFactory i records (fun r => generatedReplicaBoundaryFactoryCost r.problem r.target) hcount (by
    intro r hr
    obtain ⟨hp,ht,hl,hu,_,he,_,hpos,htarget,_⟩ := hparams r hr
    have htarget' : r.target-1 ≤ ct*Sizes.p n := by omega
    have heq : r.target-1+1 = r.target := Nat.sub_add_cancel hpos
    have hh := hf h i r.problem (r.target-1) hp ht hl hu htarget' he (by simpa only [heq] using r.sizing)
    simpa only [heq] using hh)
  have hshared : (records.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W+
      generatedReplicaBoundaryFactoryCost r.problem r.target+
      completeCachedRecoverySharedTime r.problem ((B r).problem r.sizing))).sum ≤ Sizes.T n := by
    simp_rw [List.sum_map_add]
    omega
  have hrows := recoveryInputRowSchedule_le records (Sizes.p n) cw cW spanVolume (by
    intro r hr
    obtain ⟨hp,_,_,_,_,_,_,_,_,hW⟩ := hparams r hr
    exact ⟨hp,by simpa only [hp] using (hwidths r hr).2.1,hW⟩) hspan
  have hb := hlocal h i records B N (by
    intro r hr
    obtain ⟨hp,ht,hl,hu,htarget,_,hN,_⟩ := hparams r hr
    exact ⟨hp,ht,hl,hu,htarget,hrhs r hr,hN⟩)
  have hsharedR := (Nat.cast_le (α := ℝ)).mpr hshared
  have hrowsR := (Nat.cast_le (α := ℝ)).mpr hrows
  have hvolumeR := (Nat.cast_le (α := ℝ)).mpr hvolume
  have hv := mul_le_mul_of_nonneg_left hvolumeR
    (by positivity : (0 : ℝ) ≤ F*N*(Sizes.p n : ℝ)^(129/128 : ℝ))
  have hr := mul_le_mul_of_nonneg_left hrowsR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  change _ ≤ (Sizes.T n : ℝ)+(4*cW+12*cw+28 : ℕ)*N*spanVolume*(Sizes.p n : ℝ)+
    F*N*localVolume*(Sizes.p n : ℝ)^(129/128 : ℝ)
  push_cast at hb hsharedR hr hv ⊢
  nlinarith only [hb,hsharedR,hr,hv]

/-- Overlap and guard amortization recover the selected axis-density form. -/
theorem selectedRawRecoverySchedule_density_time_le (ct cH cW : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution)
      (N band : ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        r.problem.u ≤ Sizes.p n ∧ r.problem.target ≤ cH*Sizes.p n ∧
        r.problem.rhsExp = 2 ∧ r.problem.Fs.length = N ∧
        1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1 ∧ r.W ≤ cW*Sizes.p n) →
      (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i →
      (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤ 600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2) →
      (((records.map (fun r => r.runTime (B r))).sum : ℕ) : ℝ) ≤
        Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*cH+8*2+128
  let K := 4*cW+12*cw+28
  obtain ⟨F,hF,hbound⟩ := selectedRawRecoverySchedule_time_le ct cH cW
  refine ⟨9*(K : ℝ)+600*F,by positivity,?_⟩
  filter_upwards [hbound] with n htime
  intro h i _ records B N band hcount hparams hspan hvolume
  let G := Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2
  have hb := htime h i records B N (9*Sizes.s n i) (600*G) hcount hparams hspan hvolume
  change _ ≤ (Sizes.T n : ℝ)+(K : ℕ)*N*(9*Sizes.s n i : ℕ)*(Sizes.p n : ℝ)+
    F*N*(600*G : ℕ)*(Sizes.p n : ℝ)^(129/128 : ℝ) at hb
  have hp1 : (1 : ℝ) ≤ Sizes.p n := by exact_mod_cast (show 1 ≤ Sizes.p n by have := h.thirteen_le_p; omega)
  have hpPow := Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128)
  have hs : (Sizes.s n i : ℝ) ≤ G := by exact_mod_cast (Nat.le_add_right (Sizes.s n i) _)
  have hrow := mul_le_mul hs hpPow (by positivity) (by positivity : (0 : ℝ) ≤ G)
  have hr := mul_le_mul_of_nonneg_left hrow (by positivity : (0 : ℝ) ≤ 9*(K : ℝ)*N)
  have hgap := axisGapVolume_le (band := band) (by have := h.one_le_d; omega : 0 < Sizes.d n)
    (h.good.lt i).le (h.good.bounds i)
  have hv : (G : ℝ) ≤ (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n) := by
    apply le_trans (b := ((Sizes.t n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)) ?_ hgap
    exact_mod_cast (Nat.add_le_add_right (h.good.lt i).le _)
  have hn := mul_le_mul_of_nonneg_left hv
    (by positivity : (0 : ℝ) ≤ (9*(K : ℝ)+600*F)*N*(Sizes.p n : ℝ)^(129/128 : ℝ))
  push_cast at hb ⊢
  nlinarith only [hb,hr,hn]

end IntegerMultBounds.MathlibTM2.Cost
