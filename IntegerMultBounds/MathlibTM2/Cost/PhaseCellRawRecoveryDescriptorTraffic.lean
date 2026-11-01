module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryInputStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! All descriptor serialization, loading and schedule control pay summed
shared geometry once and replica payload linearly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_map_affine {α : Type} (records : List α) (f : α → ℕ) (a b : ℕ) :
    (records.map (fun r => a+b*f r)).sum = a*records.length+b*(records.map f).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [ih]
    ring

theorem rawRecoverySchedule_inputStock_split {s : ℕ} [NeZero s]
    (records : List (RawRecoveryJob s)) (N : ℕ) (hN : ∀ r ∈ records, r.problem.Fs.length = N) :
    (records.map rawRecoveryJobInputStock).sum = (records.map rawRecoveryJobSharedInputStock).sum+
      N*(records.map rawRecoveryJobRowInputStock).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := hN r (by simp)
    have hs := ih (by intro x hx; exact hN x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    rw [rawRecoveryJobInputStock_affine,hr,hs]
    ring

theorem rawRecoverySchedule_rowInputStock_le {s : ℕ} [NeZero s]
    (records : List (RawRecoveryJob s)) (p cw cW spanVolume : ℕ)
    (hparams : ∀ r ∈ records, r.problem.p = p ∧ r.problem.wordWidth ≤ cw*p ∧ r.W ≤ cW*p)
    (hspan : (records.map (fun r => r.problem.span)).sum ≤ spanVolume) :
    (records.map rawRecoveryJobRowInputStock).sum ≤ 392*records.length+(cw+cW)*spanVolume*p := by
  have hs : (records.map rawRecoveryJobRowInputStock).sum ≤
      (records.map (fun r => 392+((cw+cW)*p)*r.problem.span)).sum := by
    apply List.sum_le_sum
    intro r hr
    obtain ⟨hp,hw,hW⟩ := hparams r hr
    have hh := rawRecoveryJobRowInputStock_le r cw cW (by rwa [hp]) (by rwa [hp])
    rw [hp] at hh
    convert hh using 1; ring
  rw [sum_map_affine] at hs
  have hv := Nat.mul_le_mul_left ((cw+cW)*p) hspan
  nlinarith only [hs,hv]

theorem selectedRawRecoverySharedInputStockSchedule_volume_le (cl cw cV cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List (RawRecoveryJob (Sizes.s n i))), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        r.problem.metadataWidth ≤ cV*r.problem.p ∧ r.problem.u ≤ r.problem.p ∧ r.W ≤ cW*r.problem.p) →
      scale*(records.map rawRecoveryJobSharedInputStock).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (392*(40000+4*cw+cl+cV)+cW+1) 1 1 scale] with n hs
  intro i _ records hcount hparams
  apply hs i records rawRecoveryJobSharedInputStock hcount
  intro r hr
  obtain ⟨hp,ht,hl,hw,hV,hu,hW⟩ := hparams r hr
  have hh := rawRecoveryJobSharedInputStock_poly_le r cl cw cV cW hl hw hV hu hW
  simpa only [hp,ht,pow_one] using hh

/-- Descriptor loading, two serialized-tape traversals and loop control have
one shared reserve, including the unary replica-count header. -/
theorem selectedRawRecoveryDescriptorTraffic_le (cl cw cV cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      {A T : ℕ} (work : Fin 392 → Fin T) (records : List (RawRecoveryJob (Sizes.s n i)))
      (N spanVolume : ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.l ≤ cl*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
        r.problem.metadataWidth ≤ cV*r.problem.p ∧ r.problem.u ≤ r.problem.p ∧ r.W ≤ cW*r.problem.p) →
      (∀ r ∈ records, r.problem.Fs.length = N) →
      (records.map (fun r => r.problem.span)).sum ≤ spanVolume →
      2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
        (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        6*records.length ≤ Sizes.T n+27*N*(392*records.length+(cw+cW)*spanVolume*Sizes.p n) := by
  filter_upwards [selectedRawRecoverySharedInputStockSchedule_volume_le cl cw cV cW 54,
    selectedDistinctCoreSetup_volume_le 20398 0 0 1] with n hshared hconstant
  intro i _ A T work records N spanVolume hcount hparams hN hspan
  have hs := hshared i records hcount hparams
  have hc := hconstant i records (fun _ => 20398) hcount (by simp)
  have hc' : 20398*records.length ≤ Sizes.T n := by
    simpa only [one_mul,List.map_const',List.sum_replicate,smul_eq_mul,Nat.mul_comm] using hc
  have hr := rawRecoverySchedule_rowInputStock_le records (Sizes.p n) cw cW spanVolume (by
    intro r hr
    obtain ⟨hp,_,_,hw,_,_,hW⟩ := hparams r hr
    exact ⟨hp,by simpa only [hp] using hw,by simpa only [hp] using hW⟩) hspan
  have htape := rawRecoverySchedule_descriptorTape_le (A := A) work records
  have hload := rawRecoverySchedule_descriptorLoad_le (A := A) work records
  rw [rawRecoverySchedule_inputStock_split records N hN] at htape hload
  have hrow := Nat.mul_le_mul_left N hr
  nlinarith only [hs,hc',htape,hload,hrow]

end IntegerMultBounds.MathlibTM2.Cost
