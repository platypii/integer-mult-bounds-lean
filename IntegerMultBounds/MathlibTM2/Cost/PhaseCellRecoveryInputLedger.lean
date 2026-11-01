module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob

/-! The executed normalization bill is affine in the actual replica count.
Keep its one-time headers separate before summing jobs over distinct cores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

def normalizeRecoveryInputSharedTime (H : ReplicaHaloProblem s) (W : ℕ) : ℕ :=
  normalizeRecoveryInputCost H W 0

def normalizeRecoveryInputRowTime (H : ReplicaHaloProblem s) (W : ℕ) : ℕ :=
  H.span*(4*W+8*(2*H.precision+8)+4*(H.precision-H.p-1)+28)

theorem normalizeRecoveryInputCost_affine (H : ReplicaHaloProblem s) (W N : ℕ) :
    normalizeRecoveryInputCost H W N = normalizeRecoveryInputSharedTime H W+N*normalizeRecoveryInputRowTime H W := by
  unfold normalizeRecoveryInputSharedTime normalizeRecoveryInputRowTime normalizeRecoveryInputCost packedInputConversionCost
  ring

/-- Conversion is linear in local payload, including common-width reading and
all shift work. No whole-axis length or replica count enters this row coefficient. -/
theorem normalizeRecoveryInputRowTime_le (H : ReplicaHaloProblem s) (W cw cW : ℕ)
    (hw : H.wordWidth ≤ cw*H.p) (hW : W ≤ cW*H.p) :
    normalizeRecoveryInputRowTime H W ≤ (4*cW+12*cw+28)*H.span*H.p := by
  have hp := H.p_pos
  have hq : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hd : H.precision-H.p-1 ≤ H.wordWidth := by omega
  have hwidth : 2*H.precision+8 = H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hc : 4*W+8*(2*H.precision+8)+4*(H.precision-H.p-1)+28 ≤ (4*cW+12*cw+28)*H.p := by
    rw [hwidth]
    nlinarith only [hw,hW,hd,hp]
  have hh := Nat.mul_le_mul_left H.span hc
  unfold normalizeRecoveryInputRowTime
  nlinarith only [hh]

/-- Header generation and retirement are linear in precision and common width. -/
theorem normalizeRecoveryInputSharedTime_le (H : ReplicaHaloProblem s) (W cw cW : ℕ)
    (hw : H.wordWidth ≤ cw*H.p) (hW : W ≤ cW*H.p) :
    normalizeRecoveryInputSharedTime H W ≤ 128*(cW+cw+2)*H.p := by
  have hp := H.p_pos
  have hq : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hd : H.precision-H.p-1 ≤ H.wordWidth := by omega
  have hwidth : 2*H.precision+8 = H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hsub : W-H.wordWidth ≤ W := Nat.sub_le _ _
  have hsub' : H.wordWidth-(H.precision-H.p-1) ≤ H.wordWidth := Nat.sub_le _ _
  unfold normalizeRecoveryInputSharedTime normalizeRecoveryInputCost packedInputConversionCost
  rw [hwidth]
  simp only [Nat.zero_mul,Nat.zero_add]
  nlinarith only [hw,hW,hp,hq,hd,hsub,hsub']

theorem rawRecoveryJob_runTime_split (r : RawRecoveryJob s)
    (B : ReplicaRecoveryBatch r.problem r.target r.solution) :
    r.runTime B = normalizeRecoveryInputSharedTime r.problem r.W+
      generatedReplicaBoundaryFactoryCost r.problem r.target+
      firstCachedReplicaRecoveryTime r.problem (B.problem r.sizing)+
      r.problem.Fs.length*normalizeRecoveryInputRowTime r.problem r.W := by
  have hN : r.problem.Fs.length = r.inputFields.length := by
    simpa only [recoveryInputFields,List.length_map] using congrArg List.length r.fields
  unfold RawRecoveryJob.runTime RawRecoveryJob.inputTime
  rw [normalizeRecoveryInputCost_affine,←hN]
  ring

/-- Splitting a uniform affine bill commutes with any structural job list. -/
private theorem recoveryScheduleTime_affine {α : Type} (records : List α) (shared row : α → ℕ) (N : ℕ) :
    (records.map (fun r => shared r+N*row r)).sum =
      (records.map shared).sum+N*(records.map row).sum := by
  induction records with
  | nil => simp
  | cons r records ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

/-- The actual normalization charges retain their affine split across the
whole job list, before any shared-volume absorption. -/
theorem rawRecoveryScheduleInputTime_split (records : List (RawRecoveryJob s)) (N : ℕ)
    (hN : ∀ r ∈ records, r.inputFields.length = N) :
    (records.map RawRecoveryJob.inputTime).sum =
      (records.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W)).sum+
        N*(records.map (fun r => normalizeRecoveryInputRowTime r.problem r.W)).sum := by
  calc
    _ = (records.map (fun r => normalizeRecoveryInputSharedTime r.problem r.W+
        N*normalizeRecoveryInputRowTime r.problem r.W)).sum := by
      congr 1
      apply List.map_congr_left
      intro r hr
      unfold RawRecoveryJob.inputTime
      rw [normalizeRecoveryInputCost_affine,hN r hr]
    _ = _ := recoveryScheduleTime_affine records _ _ N

end IntegerMultBounds.MathlibTM2.Cost
