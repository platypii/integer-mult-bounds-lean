import IntegerMultBounds.Machine.CountedLateRepairPrepare
import IntegerMultBounds.Compact.LatePowerTwoWords

/-! Literal input, output and charged costs for the uniform repair pipeline. -/
namespace IntegerMultBounds.Machine.CountedLateTapeRepairBank
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

abbrev Address (q b : ℕ) (Z : List Bool) := LateAddress (Bi b) (Li q) (controls Z).length
def width (q b : ℕ) (Z : List Bool) := Z.length*q+Z.length*b+Z.length*b
def volume (q b : ℕ) (Z : List Bool) := (Z.length+1)*(q+b+1)
def keyCost (q b : ℕ) (Z : List Bool) := 10300*volume q b Z

def records (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  repairRecords (lateRankEquiv q b Z) (lateSperm q b Z) data

def extracted (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  Compact.items (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z) (lateBadSet q b Z) (width q b Z) data

def flagged (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  stream (lateRankEquiv q b Z) (lateBadSet q b Z) (data ∘ (lateSperm q b Z).symm)

def ideal (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  stream (lateRankEquiv q b Z) (lateBadSet q b Z) (data ∘ (lateTperm q b Z).symm)

def replacements (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  (sortedExtracted (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z) (lateBadSet q b Z) (width q b Z) data).map Prod.snd

def input (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :=
  CountedLateRepairPrepare.input (RepairScan.srcTape (records q b Z data)) Z hs

def prepared (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :=
  CountedLateRepairPrepare.bank (width q b Z) (RepairScan.srcTape (records q b Z data)) Z hs

def output (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) : Tapes 46 1 :=
  ((RepairStage.stage (width q b Z)
    (TapeRadixSort.completed (width q b Z) (RepairStage.raw (extracted q b Z data)))
    (RepairStage.sortedRaw (width q b Z) (extracted q b Z data))
    (KeySelect.encode (RepairStage.sortedRaw (width q b Z) (extracted q b Z data))).length 0
    (RepairStage.encTape (Partition.encode (replacements q b Z data)))
    (Partition.encode (replacements q b Z data)).length
    (RepairStage.encTape (Partition.encode (flagged q b Z data)))
    (Partition.encode (flagged q b Z data)).length
    (RepairStage.encTape (Partition.encode (ideal q b Z data)))
    (Partition.encode (ideal q b Z data)).length).append
    (RepairScan.tail (records q b Z data) (width q b Z) (lateMi q b Z))).append
    (CountedLateRepairScanBank.scratch Z hs)

def scanCost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  lateMi q b Z*(keyCost q b Z+10)+3*(Partition.encode (flagged q b Z data)).length+
    (74*width q b Z+5)*(KeySelect.encode (RepairStage.raw (extracted q b Z data))).length+
    (2*width q b Z+3)*Nat.card {x // lateBadSet q b Z x}+width q b Z+14

def cost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  2004*volume q b Z+scanCost q b Z data+1

theorem ideal_preserves (q b : ℕ) (Z : List Bool) (y : Address q b Z) :
    lateBadSet q b Z (lateTperm q b Z y) ↔ lateBadSet q b Z y :=
  not_congr (lateIdeal_preserves_good (Bi b) (Li q) (Li_pos q) (controls Z) (controls_bits Z) y)

theorem program_agrees (q b : ℕ) (Z : List Bool) (y : Address q b Z)
    (hy : ¬ lateBadSet q b Z y) : lateSperm q b Z y=lateTperm q b Z y :=
  late_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q)
    (controls Z) (controls_bits Z) y (not_not.mp hy)

theorem capacity (q b : ℕ) (Z : List Bool) (hq : 1≤q) : lateMi q b Z≤2^(width q b Z) := by
  rw [lateMi_eq q b Z hq]
  exact le_refl _

theorem output_ideal (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    (output q b Z hs data).tape 10=RepairStage.encTape (Partition.encode (ideal q b Z data)) := rfl

theorem output_scratch (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool)
    (i : Fin 32) :
    (output q b Z hs data).tape (Fin.natAdd 14 i)=(CountedLateRepairScanBank.scratch Z hs).tape i ∧
      (output q b Z hs data).head (Fin.natAdd 14 i)=(CountedLateRepairScanBank.scratch Z hs).head i := by
  simp only [output,Tapes.append,Fin.addCases_right]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.CountedLateTapeRepairBank
