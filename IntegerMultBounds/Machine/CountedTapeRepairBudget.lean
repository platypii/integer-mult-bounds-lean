import IntegerMultBounds.Machine.CountedTapeRepairCleanupRun

/-! Uniform paid repair bounds in record width and exceptional count/density. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairBudget
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo
open CountedTapeRepairBank

def badCount (q b : ℕ) (Z : List Bool) := Nat.card {x // badSet q b Z x}
def extractedVolume (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  (KeySelect.encode (RepairStage.raw (CountedTapeRepairBank.extracted q b Z data))).length

theorem encode_volume (rs : List Partition.Record) (w : ℕ) (hw : ∀ r ∈ rs,r.payload.length≤w) :
    (Partition.encode rs).length≤rs.length*(w+2) := by
  induction rs with
  | nil => simp [Partition.encode]
  | cons r rs ih =>
    have hr := hw r (by simp)
    have hi := ih (by intro x hx; exact hw x (by simp [hx]))
    simp only [Partition.encode,List.length_append,Partition.recordWord,List.length_cons,List.length_map,List.length_nil]
    nlinarith

theorem stream_volume {α : Type*} {M : ℕ} (e : α ≃ Fin M) (bad : α → Prop) [DecidablePred bad]
    (data : α → List Bool) (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    (Partition.encode (stream e bad data)).length≤M*(w+2) := by
  have h := encode_volume (stream e bad data) w (by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact hw _)
  simpa only [stream,List.length_map,List.length_finRange] using h

theorem plain_volume {α : Type*} {M : ℕ} (e : α ≃ Fin M)
    (data : α → List Bool) (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    (Partition.encode (plain e data)).length≤M*(w+2) := by
  have h := encode_volume (plain e data) w (by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact hw _)
  simpa only [plain,List.length_map,List.length_finRange] using h

theorem extracted_volume (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool)
    (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    extractedVolume q b Z data≤badCount q b Z*(width q b Z+2+w) := by
  exact items_volume_le (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (badSet q b Z) (width q b Z) data w (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hw _)

theorem replacement_volume (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool)
    (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    (Partition.encode (replacements q b Z data)).length≤badCount q b Z*(w+2) := by
  have hl : (replacements q b Z data).length=badCount q b Z := by
    unfold replacements sortedExtracted
    rw [List.length_map,(RadixSort.sort_perm _ _ _).length_eq,extracted_length]
    rfl
  rw [← hl]
  apply encode_volume
  intro r hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  have hx' : x ∈ Compact.extracted (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (badSet q b Z) data :=
    (RadixSort.sort_perm _ _ _).mem_iff.mp hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx'
  exact hw _

theorem sorted_volume (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :
    (CountedTapeRepairCleanupRun.sortedWord q b Z data).length=extractedVolume q b Z data :=
  TapeRadixSort.volume_sort _ _

theorem index_le (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :
    CountedTapeRepairCleanupRun.index q b Z data≤width q b Z := by
  unfold CountedTapeRepairCleanupRun.index TapeRadixSort.completed
  split <;> omega

def fullCost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  CountedTapeRepairBank.cost q b Z data+1+CountedTapeRepairCleanupRun.cost q b Z data

def base (q b : ℕ) (Z : List Bool) (w : ℕ) :=
  1004*volume q b Z+Mi q b Z*(keyCost q b Z+10)+6*Mi q b Z*(w+2)+7*width q b Z+88

def coefficient (q b : ℕ) (Z : List Bool) (w : ℕ) :=
  (74*width q b Z+7)*(width q b Z+2+w)+2*width q b Z+3

def bound (q b : ℕ) (Z : List Bool) (w D : ℕ) := base q b Z w+D*coefficient q b Z w

theorem full_cost_le (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool)
    (w : ℕ) (hw : ∀ x,(data x).length≤w) :
    fullCost q b Z data≤bound q b Z w (badCount q b Z) := by
  have hF := stream_volume (rankEquiv q b Z) (badSet q b Z) (data ∘ (Sperm q b Z).symm) w (fun x => hw _)
  have hI := stream_volume (rankEquiv q b Z) (badSet q b Z) (data ∘ (Tperm q b Z).symm) w (fun x => hw _)
  have hS := plain_volume (rankEquiv q b Z) (data ∘ (Sperm q b Z).symm) w (fun x => hw _)
  have hE := extracted_volume q b Z data w hw
  have hR := replacement_volume q b Z data w hw
  have hidx := index_le q b Z data
  have hslen := CountedTapeRepairCleanupRun.record_length (records q b Z data)
  change (DropFlag.encode (records q b Z data)).length=_ at hslen
  change (Partition.encode (flagged q b Z data)).length≤_ at hF
  change (Partition.encode (ideal q b Z data)).length≤_ at hI
  change (Partition.encode (records q b Z data)).length≤_ at hS
  have hsort := Nat.mul_le_mul_left (74*width q b Z+6) hE
  unfold fullCost CountedTapeRepairBank.cost scanCost CountedTapeRepairCleanupRun.cost
  rw [sorted_volume]
  change _≤bound q b Z w (badCount q b Z)
  unfold bound base coefficient badCount extractedVolume at *
  nlinarith

theorem count_bound (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool)
    (w D : ℕ) (hw : ∀ x,(data x).length≤w) (hD : badCount q b Z≤D) :
    fullCost q b Z data≤bound q b Z w D :=
  (full_cost_le q b Z data w hw).trans (by unfold bound; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hD) _)

theorem density_bound (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool)
    (w numerator denominator : ℕ) (hw : ∀ x,(data x).length≤w)
    (hD : denominator*badCount q b Z≤numerator*Mi q b Z) :
    denominator*fullCost q b Z data≤denominator*base q b Z w+
      numerator*Mi q b Z*coefficient q b Z w := by
  have h1 := Nat.mul_le_mul_left denominator (full_cost_le q b Z data w hw)
  have h2 := Nat.mul_le_mul_right (coefficient q b Z w) hD
  unfold bound at h1
  nlinarith

end
end IntegerMultBounds.Machine.CountedTapeRepairBudget
