module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! Pay normalization setup once over all distinct cores and conversion work
by the actual sum of halo spans, retaining the replica factor explicitly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_map_le_scaled {α : Type} (records : List α) (cost weight : α → ℕ) (C : ℕ)
    (h : ∀ r ∈ records, cost r ≤ C*weight r) :
    (records.map cost).sum ≤ C*(records.map weight).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := h r (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hr,hs]

theorem recoveryInputRowSchedule_le {s : ℕ} [NeZero s]
    (records : List (RawRecoveryJob s)) (p cw cW volume : ℕ)
    (hparams : ∀ r ∈ records, r.problem.p = p ∧ r.problem.wordWidth ≤ cw*p ∧ r.W ≤ cW*p)
    (hvolume : (records.map (fun r => r.problem.span)).sum ≤ volume) :
    (records.map (fun r => normalizeRecoveryInputRowTime r.problem r.W)).sum ≤
      (4*cW+12*cw+28)*volume*p := by
  have hs := sum_map_le_scaled records
    (fun r => normalizeRecoveryInputRowTime r.problem r.W) (fun r => r.problem.span) ((4*cW+12*cw+28)*p)
    (by
      intro r hr
      obtain ⟨hp,hw,hW⟩ := hparams r hr
      have hh := normalizeRecoveryInputRowTime_le r.problem r.W cw cW (by rwa [hp]) (by rwa [hp])
      rw [hp] at hh
      convert hh using 1 <;> ring)
  have hv := Nat.mul_le_mul_left ((4*cW+12*cw+28)*p) hvolume
  nlinarith only [hs,hv]

/-- All normalization headers and retirement across the core list fit one
shared volume reserve; the numerical fields do not multiply this bill. -/
theorem selectedRecoveryInputSharedSchedule_volume_le (cw cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i))), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.wordWidth ≤ cw*Sizes.p n ∧ r.W ≤ cW*Sizes.p n) →
      scale*(records.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W)).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (128*(cW+cw+2)) 1 0 scale] with n hs
  intro i _ records hcount hparams
  apply hs i records (fun r => normalizeRecoveryInputSharedTime r.problem r.W) hcount
  intro r hr
  obtain ⟨hp,hw,hW⟩ := hparams r hr
  have hh := normalizeRecoveryInputSharedTime_le r.problem r.W cw cW (by rwa [hp]) (by rwa [hp])
  simpa only [hp,pow_zero,pow_one,Nat.mul_one] using hh

/-- The executed input normalization schedule costs one shared reserve plus
linear replica payload. The halo-volume estimate can be supplied separately. -/
theorem selectedRecoveryInputSchedule_le (cw cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i))) (N volume : ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.wordWidth ≤ cw*Sizes.p n ∧ r.W ≤ cW*Sizes.p n) →
      (∀ r ∈ records, r.inputFields.length = N) →
      (records.map (fun r => r.problem.span)).sum ≤ volume →
      (records.map RawRecoveryJob.inputTime).sum ≤ Sizes.T n+(4*cW+12*cw+28)*N*volume*Sizes.p n := by
  filter_upwards [selectedRecoveryInputSharedSchedule_volume_le cw cW 1] with n hs
  intro i _ records N volume hcount hparams hN hvolume
  have hshared := hs i records hcount hparams
  simp only [one_mul] at hshared
  have hrows := recoveryInputRowSchedule_le records (Sizes.p n) cw cW volume hparams hvolume
  rw [rawRecoveryScheduleInputTime_split records N hN]
  nlinarith only [hshared,Nat.mul_le_mul_left N hrows]

end IntegerMultBounds.MathlibTM2.Cost
