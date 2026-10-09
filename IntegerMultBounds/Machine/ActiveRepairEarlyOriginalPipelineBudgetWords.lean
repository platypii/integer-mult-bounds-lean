import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint
import IntegerMultBounds.Machine.CountedTapeRepairBudget

/-! Word-volume bounds for physical flag/extract/sort/reinsert cleanup.
These list lemmas will be instantiated with the actual early/later key programs. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetWords
noncomputable section

theorem flagged_payloads (flag : ℕ → Bool) (rs : List Partition.Record) (R j : ℕ)
    (hw : ∀ r ∈ rs,r.payload.length≤R) :
    ∀ r ∈ RepairScan.flagged flag j rs,r.payload.length≤R := by
  induction rs generalizing j with
  | nil => simp [RepairScan.flagged]
  | cons r rs ih =>
    intro x hx
    simp only [RepairScan.flagged,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact hw r (by simp)
    · exact ih (j+1) (by intro y hy; exact hw y (by simp [hy])) x hx

theorem item_payloads (flag : ℕ → Bool) (bits : ℕ → List Bool)
    (rs : List Partition.Record) (R j : ℕ) (hw : ∀ r ∈ rs,r.payload.length≤R) :
    ∀ x ∈ RepairScan.items flag bits j rs,x.2.payload.length≤R := by
  induction rs generalizing j with
  | nil => simp [RepairScan.items]
  | cons r rs ih =>
    intro x hx
    simp only [RepairScan.items,List.mem_append] at hx
    rcases hx with hx|hx
    · cases hf : flag j with
      | false => simp [hf] at hx
      | true =>
        simp only [hf,ite_true,List.mem_singleton] at hx
        subst x
        exact hw r (by simp)
    · exact ih (j+1) (by intro y hy; exact hw y (by simp [hy])) x hx

theorem replacement_payloads (A : ℕ) (its : List RepairStage.Keyed) (R : ℕ)
    (hw : ∀ x ∈ its,x.2.payload.length≤R) :
    ∀ r ∈ RepairStage.replacements A its,r.payload.length≤R := by
  intro r hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  exact hw x ((RadixSort.sort_perm _ _ _).mem_iff.mp hx)

theorem volumes (A R : ℕ) (rs : List Partition.Record) (flag : ℕ → Bool) (bits : ℕ → List Bool)
    (hw : ∀ r ∈ rs,r.payload.length≤R) (hb : ∀ j,(bits j).length=A) :
    let its := RepairScan.items flag bits 0 rs
    let fl := RepairScan.flagged flag 0 rs
    let H := Reinsert.holes fl
    (DropFlag.encode rs).length≤rs.length*(R+2) ∧
    (Partition.encode fl).length≤rs.length*(R+2) ∧
    (KeySelect.encode (RepairStage.raw its)).length≤H*(A+R+2) ∧
    (Partition.encode (RepairStage.replacements A its)).length≤H*(R+2) ∧
    (Partition.encode (Reinsert.fill fl (RepairStage.replacements A its))).length≤2*rs.length*(R+2) ∧
    H≤rs.length := by
  dsimp only
  let its := RepairScan.items flag bits 0 rs
  let fl := RepairScan.flagged flag 0 rs
  have hF := CountedTapeRepairBudget.encode_volume fl R (flagged_payloads flag rs R 0 hw)
  rw [RepairScan.flagged_length] at hF
  have hS := CountedTapeRepairBudget.encode_volume rs R hw
  have he : (DropFlag.encode rs).length=(Partition.encode rs).length := by
    rw [DropFlag.encode_partition,List.length_map]
  have hi : its.length=Reinsert.holes fl := RepairScan.items_length flag bits 0 rs
  have hK : ∀ x ∈ its,x.1.length=A := RepairScan.items_keys flag bits A 0 rs (fun i _ _ => hb i)
  have hP := item_payloads flag bits rs R 0 hw
  have hE := RepairStage.raw_volume_le A its hK R hP
  rw [hi] at hE
  have hL : (RepairStage.replacements A its).length=Reinsert.holes fl := by
    rw [RepairStage.replacements,RepairStage.sortedItems,List.length_map,
      (RadixSort.sort_perm _ _ _).length_eq,hi]
  have hR := CountedTapeRepairBudget.encode_volume (RepairStage.replacements A its) R
    (replacement_payloads A its R hP)
  rw [hL] at hR
  have hH : Reinsert.holes fl≤rs.length := by
    exact (List.length_filter_le _ fl).trans (RepairScan.flagged_length flag 0 rs).le
  have hI := Reinsert.fill_volume fl (RepairStage.replacements A its) hL
  have hB := Partition.bucket_lengths fl
  have hHR := Nat.mul_le_mul_right (R+2) hH
  exact ⟨by omega,hF,by simpa only [Nat.add_assoc,Nat.add_comm R 2] using hE,hR,
    by
      change (Partition.encode (Reinsert.fill fl (RepairStage.replacements A its))).length≤_
      nlinarith,hH⟩

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetWords
