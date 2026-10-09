import IntegerMultBounds.Machine.CountedLateTapeRepairCleanup
import IntegerMultBounds.Machine.CountedLateTapeRepairBank

/-! Concrete final cleanup of the actual repair endpoint, including all sort
markers, unary metadata and counter, retaining only caller inputs and output. -/
namespace IntegerMultBounds.Machine.CountedLateTapeRepairCleanupRun
noncomputable section
open SharedPlacementAlphabet
open CountedLateTapeRepairBank
open CountedTapeRepairCleanupWord

def recordWord (rs : List Partition.Record) := DropFlag.encode rs

theorem record_tape (rs : List Partition.Record) :
    putWord (fun _ => blank) 0 (recordWord rs)=RepairStage.encTape (Partition.encode rs) := by
  rw [recordWord,DropFlag.encode_partition]
  exact RepairStage.encTape_eq _

theorem record_length (rs : List Partition.Record) : (recordWord rs).length=(Partition.encode rs).length := by
  rw [recordWord,DropFlag.encode_partition,List.length_map]

theorem record_nonblank (rs : List Partition.Record) : ∀ x ∈ recordWord rs,x≠blank :=
  fun x hx => (MarkedReturn.dropFlag_interior rs x hx).1

theorem selector_marked (k : ℕ) : KeySelect.selector k=marked (List.replicate k (bitSymbol true)) := by
  rw [← CountedRepairScanPrepare.selector_filled]
  unfold CountedRepairScanMetadataRun.filled marked
  congr 1
  funext z
  by_cases hz : z = -1
  · simp [hz,KeySelect.selector,PartitionMarked.markedTape]
  · simp only [KeySelect.selector,hz,ite_false]
    rw [ite_eq_right (by omega : ¬(0≤z ∧ z<(0 : ℕ)))]
    simp only [PartitionMarked.markedTape,putWord]
    change blank=(if z = -1 then PartitionMarked.marker else PartitionMarked.encoding.encode blank)
    rw [ite_eq_right hz]
    rfl

def index (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  TapeRadixSort.completed (width q b Z) (RepairStage.raw (extracted q b Z data))

def sortedWord (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  KeySelect.encode (RepairStage.sortedRaw (width q b Z) (extracted q b Z data))

def counter (q b : ℕ) (Z : List Bool) := RepairScan.counter (width q b Z) (Compact.PowerTwo.lateMi q b Z)

def cleaned (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :=
  setTape (CountedLateTapeRepairBank.input q b Z hs data) 10 (RepairStage.encTape (Partition.encode (ideal q b Z data))) 0

def cost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  (sortedWord q b Z data).length+2*index q b Z data+4*width q b Z+
    (Partition.encode (replacements q b Z data)).length+
    (Partition.encode (flagged q b Z data)).length+
    (Partition.encode (ideal q b Z data)).length+
    (DropFlag.encode (records q b Z data)).length+72

theorem clean_output (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    CountedLateTapeRepairCleanup.output (CountedLateTapeRepairBank.output q b Z hs data)
      (recordWord (ideal q b Z data)) (recordWord (records q b Z data))=cleaned q b Z hs data := by
  unfold cleaned
  rw [← record_tape]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    HoareTime CountedLateTapeRepairCleanup.program (fun v => v=CountedLateTapeRepairBank.output q b Z hs data)
      (fun v => v=cleaned q b Z hs data) (cost q b Z data) := by
  let v := CountedLateTapeRepairBank.output q b Z hs data
  have h8 : v.tape 8=putWord (fun _ => blank) 0 (recordWord (replacements q b Z data)) := (record_tape _).symm
  have h9 : v.tape 9=putWord (fun _ => blank) 0 (recordWord (flagged q b Z data)) := (record_tape _).symm
  have h10 : v.tape 10=putWord (fun _ => blank) 0 (recordWord (ideal q b Z data)) := (record_tape _).symm
  have hp8 : v.head 8=(recordWord (replacements q b Z data)).length := by rw [record_length]; rfl
  have hp9 : v.head 9=(recordWord (flagged q b Z data)).length := by rw [record_length]; rfl
  have hp10 : v.head 10=(recordWord (ideal q b Z data)).length := by rw [record_length]; rfl
  have h := CountedLateTapeRepairCleanup.runs v (sortedWord q b Z data)
    (List.replicate (index q b Z data) (bitSymbol true)) (List.replicate (width q b Z) (bitSymbol true))
    (recordWord (replacements q b Z data)) (recordWord (flagged q b Z data)) (recordWord (ideal q b Z data))
    (recordWord (records q b Z data)) (counter q b Z)
    rfl rfl (selector_marked _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (selector_marked _) rfl
    h8 hp8 h9 hp9 h10 hp10 rfl rfl rfl rfl rfl rfl
    (RepairStage.encode_nonblank _) (by intro x hx; simp only [List.mem_replicate] at hx; rcases hx with ⟨_,rfl⟩; decide)
    (by intro x hx; simp only [List.mem_replicate] at hx; rcases hx with ⟨_,rfl⟩; decide)
    (record_nonblank _) (record_nonblank _) (record_nonblank _) (record_nonblank _)
  rw [clean_output] at h
  simp only [List.length_replicate,record_length,counter,RepairScan.counter_length] at h
  have hR := record_length (replacements q b Z data)
  have hF := record_length (flagged q b Z data)
  have hI := record_length (ideal q b Z data)
  have hS := record_length (records q b Z data)
  change (DropFlag.encode (records q b Z data)).length=_ at hS
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.CountedLateTapeRepairCleanupRun
