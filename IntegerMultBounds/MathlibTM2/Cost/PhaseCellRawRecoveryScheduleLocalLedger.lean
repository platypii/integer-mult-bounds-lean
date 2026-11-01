module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCompleteCachedRecoveryLocalLedger

/-! Sum actual raw-job costs before applying shared setup and halo-overlap bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_local_bills_le {α : Type} (records : List α)
    (time shared row volume : α → ℕ) (N : ℕ) (F P : ℝ)
    (hcost : ∀ r ∈ records, (time r : ℝ) ≤ shared r+N*(row r : ℝ)+F*N*(volume r : ℝ)*P) :
    ((records.map time).sum : ℝ) ≤ (records.map shared).sum+
      N*((records.map row).sum : ℝ)+F*N*((records.map volume).sum : ℝ)*P := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := hcost r (by simp)
    have hs := ih (by intro x hx; exact hcost x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    simp only [Nat.cast_add]
    nlinarith only [hr,hs]

/-- The actual executed raw-job bills sum with one replica factor and the sum
of local halo volumes; no whole-axis bill is multiplied by the core count. -/
theorem selectedRawRecoverySchedule_local_ledger_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution)
      (N : ℕ),
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        r.problem.u ≤ Sizes.p n ∧ r.problem.target ≤ ct*Sizes.p n ∧
        r.problem.rhsExp ≤ ce*Sizes.p n ∧ r.problem.Fs.length = N) →
      (((records.map (fun r => r.runTime (B r))).sum : ℕ) : ℝ) ≤
        (records.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W+
          generatedReplicaBoundaryFactoryCost r.problem r.target+
          completeCachedRecoverySharedTime r.problem ((B r).problem r.sizing))).sum+
        N*((records.map (fun r => normalizeRecoveryInputRowTime r.problem r.W)).sum : ℝ)+
        F*N*((records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum : ℝ)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hbound⟩ := selectedRawRecoveryJob_local_ledger_le ct ce
  refine ⟨F,hF,?_⟩
  intro n h i _ records B N hparams
  apply sum_local_bills_le
  intro r hr
  obtain ⟨hp,ht,hl,hu,htarget,hrhs,hN⟩ := hparams r hr
  have hc := hbound h i r hp ht hl hu htarget hrhs (B r)
  simpa only [hN,hp] using hc

end IntegerMultBounds.MathlibTM2.Cost
