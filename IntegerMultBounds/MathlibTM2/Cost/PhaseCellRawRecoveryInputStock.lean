module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorScheduleVolume

/-! Price the actual raw input bank and its serialized descriptor structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem registerBankStock_updateRight_le {T A : ℕ} (S : Stacks T A)
    (k : Fin T) (xs : List (Fin (A+4))) :
    registerBankStock {S with R := Function.update S.R k xs} ≤ registerBankStock S+xs.length := by
  have h (i : Fin T) : (S.L i).length+(Function.update S.R k xs i).length ≤
      (S.L i).length+(S.R i).length+if i = k then xs.length else 0 := by
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self,ite_true]
      omega
    · simp only [Function.update_of_ne hi,hi,ite_false,Nat.add_zero]
      exact le_refl _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simpa only [registerBankStock,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hs

theorem rawRecoveryInput_stock_le {s A : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (W : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    registerBankStock (rawRecoveryInput (A := A) H W Fs [] []) ≤
      generatedRecoveryInputStock H [] []+Fs.length*H.span*W+H.p+W := by
  let I := generatedRecoveryInput (A := A) H [] []
  let xs := cstream A W (Fs.map (packedInterval H.origin H.span)).flatten
  have hlen : xs.length = Fs.length*H.span*W := by
    dsimp only [xs]
    rw [length_cstream,packedBatch_length H.origin H.span Fs H.span_fit]
  let v : HS 392 1 A Unit := ⟨false,none,0,fun _ => 0,none,()⟩
  have hg := generatedRecoveryInput_stock_le H [] [] v
  rw [mnSize_mk_registerBankStock] at hg
  change 0+0+registerBankStock I ≤ generatedRecoveryInputStock H [] [] at hg
  have h₁ := registerBankStock_updateRight_le I 124 xs
  have h₂ := registerBankStock_updateRight_le {I with R := Function.update I.R 124 xs} 129
    (List.replicate H.p tick)
  have h₃ := registerBankStock_updateRight_le
    {I with R := Function.update (Function.update I.R 124 xs) 129 (List.replicate H.p tick)} 130
    (List.replicate W tick)
  change registerBankStock {I with R := (Function.update (Function.update (Function.update I.R 124 xs)
    129 (List.replicate H.p tick)) 130 (List.replicate W tick))} ≤ _
  simp only [List.length_replicate,hlen] at h₁ h₂ h₃
  omega

/-- An explicit bank allowance: one shared header bank and the raw and
normalized payloads, with the two disposable input-format headers. -/
def rawRecoveryJobInputStock {s : ℕ} [NeZero s] (r : RawRecoveryJob s) : ℕ :=
  generatedRecoveryInputStock r.problem [] []+r.inputFields.length*r.problem.span*r.W+r.problem.p+r.W

theorem rawRecoveryJob_initialStock_le {s A : ℕ} [NeZero s] (r : RawRecoveryJob s) :
    r.initialStock (A := A) ≤ rawRecoveryJobInputStock r :=
  rawRecoveryInput_stock_le r.problem r.W r.inputFields

theorem rawRecoveryJob_descriptorVolume_le {s A : ℕ} [NeZero s] (r : RawRecoveryJob s) :
    (∑ i, (r.words (A := A) i).length) ≤ rawRecoveryJobInputStock r := by
  have hs := rawRecoveryJob_initialStock_le (A := A) r
  unfold RawRecoveryJob.initialStock at hs
  rw [registerBankStock_eq_right_sum _ (by intro i; rfl)] at hs
  exact hs

theorem rawRecoveryJob_descriptorLoad_le {s A T : ℕ} [NeZero s] (r : RawRecoveryJob s)
    (work : Fin 392 → Fin T) :
    takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))) ≤ 23*rawRecoveryJobInputStock r+9409 := by
  rw [takePlacedDescriptorBankCost_eq]
  have hs := rawRecoveryJob_descriptorVolume_le (A := A) r
  omega

/-- The replica-count header is removed from shared geometry and charged in
its row allowance, alongside the two packed payload formats. -/
def rawRecoveryJobSharedInputStock {s : ℕ} [NeZero s] (r : RawRecoveryJob s) : ℕ :=
  392*(generatedRecoveryHeaderStock r.problem-r.problem.Fs.length)+r.problem.p+r.W

def rawRecoveryJobRowInputStock {s : ℕ} [NeZero s] (r : RawRecoveryJob s) : ℕ :=
  392+r.problem.span*(r.problem.wordWidth+r.W)

theorem rawRecoveryJobInputStock_affine {s : ℕ} [NeZero s] (r : RawRecoveryJob s) :
    rawRecoveryJobInputStock r = rawRecoveryJobSharedInputStock r+
      r.problem.Fs.length*rawRecoveryJobRowInputStock r := by
  have hN : r.problem.Fs.length = r.inputFields.length := by
    simpa only [recoveryInputFields,List.length_map] using congrArg List.length r.fields
  have hheader : generatedRecoveryHeaderStock r.problem =
      (generatedRecoveryHeaderStock r.problem-r.problem.Fs.length)+r.problem.Fs.length := by
    have hh : r.problem.Fs.length ≤ generatedRecoveryHeaderStock r.problem := by
      unfold generatedRecoveryHeaderStock
      omega
    omega
  unfold rawRecoveryJobInputStock generatedRecoveryInputStock rawRecoveryJobSharedInputStock rawRecoveryJobRowInputStock
  simp only [List.length_nil,Nat.zero_add]
  rw [←hN]
  nlinarith only [hheader]

theorem rawRecoveryJobRowInputStock_le {s : ℕ} [NeZero s] (r : RawRecoveryJob s) (cw cW : ℕ)
    (hw : r.problem.wordWidth ≤ cw*r.problem.p) (hW : r.W ≤ cW*r.problem.p) :
    rawRecoveryJobRowInputStock r ≤ 392+(cw+cW)*r.problem.span*r.problem.p := by
  have hh := Nat.mul_le_mul_left r.problem.span (Nat.add_le_add hw hW)
  unfold rawRecoveryJobRowInputStock
  nlinarith only [hh]

theorem rawRecoveryJobSharedInputStock_poly_le {s : ℕ} [NeZero s] (r : RawRecoveryJob s)
    (cl cw cV cW : ℕ) (hl : r.problem.l ≤ cl*r.problem.p)
    (hw : r.problem.wordWidth ≤ cw*r.problem.p) (hV : r.problem.metadataWidth ≤ cV*r.problem.p)
    (hu : r.problem.u ≤ r.problem.p) (hW : r.W ≤ cW*r.problem.p) :
    rawRecoveryJobSharedInputStock r ≤
      (392*(40000+4*cw+cl+cV)+cW+1)*r.problem.t*r.problem.p := by
  let H := r.problem
  let Y := H.t*H.p
  have hp := H.p_pos
  have ht : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hpY : H.p ≤ Y := Nat.le_mul_of_pos_left _ ht
  have htY : H.t ≤ Y := Nat.le_mul_of_pos_right _ hp
  have hwY : H.wordWidth ≤ cw*Y := hw.trans (Nat.mul_le_mul_left cw hpY)
  have hlY : H.l ≤ cl*Y := hl.trans (Nat.mul_le_mul_left cl hpY)
  have hVY : H.metadataWidth ≤ cV*Y := hV.trans (Nat.mul_le_mul_left cV hpY)
  have hWY : r.W ≤ cW*Y := hW.trans (Nat.mul_le_mul_left cW hpY)
  have hq : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hstage : H.stage+1 ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.stage ReplicaHaloProblem.wordWidth executionStagePrecision executionWidth
    omega
  have hs : s ≤ H.t := H.s_lt_t.le
  have hb : H.band ≤ H.t := (H.band_fit : H.band ≤ s).trans hs
  have ho : H.origin ≤ H.t := by have := H.span_fit; omega
  have he : H.origin+H.span ≤ H.t := H.span_fit.trans hs
  have hspan : H.span ≤ H.t := by omega
  have hline : H.span*H.wordWidth ≤ cw*Y := by
    have hh := Nat.mul_le_mul hspan hw
    dsimp only [Y]
    nlinarith only [hh]
  have hheader : (generatedRecoveryHeaderStock H-H.Fs.length)+H.Fs.length =
      generatedRecoveryHeaderStock H := by
    apply Nat.sub_add_cancel
    unfold generatedRecoveryHeaderStock
    omega
  have hg : generatedRecoveryHeaderStock H-H.Fs.length ≤ (40000+4*cw+cl+cV)*Y := by
    unfold generatedRecoveryHeaderStock at hheader ⊢
    rw [show (2 : ℕ)^15 = 32768 by decide] at hheader ⊢
    nlinarith only [hheader,hpY,htY,hwY,hlY,hVY,hq,hstage,hs,hb,ho,he,hline,hu]
  have hh := Nat.mul_le_mul_left 392 hg
  change 392*(generatedRecoveryHeaderStock H-H.Fs.length)+H.p+r.W ≤ _
  change _ ≤ (392*(40000+4*cw+cl+cV)+cW+1)*H.t*H.p
  dsimp only [Y] at hh hpY hWY
  nlinarith only [hh,hpY,hWY]

private theorem sum_map_affine_le {α : Type} (records : List α) (cost volume : α → ℕ)
    (a b : ℕ) (h : ∀ r ∈ records, cost r ≤ a*volume r+b) :
    (records.map cost).sum ≤ a*(records.map volume).sum+b*records.length := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := h r (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hr,hs]

theorem rawRecoverySchedule_descriptorTape_le {s A T : ℕ} [NeZero s]
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    (descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length ≤
      2*(records.map rawRecoveryJobInputStock).sum+392*records.length := by
  rw [descriptorScheduleTape_length]
  apply sum_map_affine_le
  intro r _
  have hs := rawRecoveryJob_descriptorVolume_le (A := A) r
  omega

theorem rawRecoverySchedule_descriptorLoad_le {s A T : ℕ} [NeZero s]
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum ≤
      23*(records.map rawRecoveryJobInputStock).sum+9409*records.length := by
  apply sum_map_affine_le
  intro r _
  exact rawRecoveryJob_descriptorLoad_le r work

end IntegerMultBounds.MathlibTM2.Cost
