import IntegerMultBounds.Machine.CountedTapeRepairDensity

/-! Complete reusable fixed-control repair endpoint: physical metadata setup,
keyed scan, radix sort, reinsertion, and physical removal of all stage work. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairEndpoint
noncomputable section
open SharedPlacementAlphabet
open CountedTapeRepairBank
open CountedTapeRepairBudget
open CountedTapeRepairCleanupRun (cleaned)

def program := seq CountedTapeRepairRun.program CountedTapeRepairCleanup.program

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (data : Address q b Z → List Bool) :
    HoareTime program (fun v => v=CountedTapeRepairBank.input q b Z hs data)
      (fun v => v=cleaned q b Z hs data) (fullCost q b Z data) :=
  (CountedTapeRepairRun.runs q b hb hbq Z hs hv hc data).seq
    (CountedTapeRepairCleanupRun.runs q b Z hs data)

theorem runs_bounded (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (data : Address q b Z → List Bool)
    (w D : ℕ) (hw : ∀ x,(data x).length≤w) (hD : badCount q b Z≤D) :
    HoareTime program (fun v => v=CountedTapeRepairBank.input q b Z hs data)
      (fun v => v=cleaned q b Z hs data) (bound q b Z w D) :=
  (runs q b hb hbq Z hs hv hc data).consequence (fun _ h => h) (fun _ h => h)
    (count_bound q b Z data w D hw hD)

theorem ideal_output (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    (cleaned q b Z hs data).tape 10=RepairStage.encTape (Partition.encode (ideal q b Z data)) ∧
      (cleaned q b Z hs data).head 10=0 := by
  constructor <;> rfl

theorem source_retained (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    (cleaned q b Z hs data).tape 11=RepairScan.srcTape (records q b Z data) ∧
      (cleaned q b Z hs data).head 11=0 := by
  constructor <;> rfl

theorem work_blank (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool)
    (i : Fin 14) (h10 : i≠10) (h11 : i≠11) :
    (cleaned q b Z hs data).tape (Fin.castAdd 28 i)=(fun _ => blank) ∧
      (cleaned q b Z hs data).head (Fin.castAdd 28 i)=0 := by
  fin_cases i <;> first | (exact ⟨rfl,rfl⟩) | contradiction

theorem scratch_retained (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool)
    (i : Fin 28) :
    (cleaned q b Z hs data).tape (Fin.natAdd 14 i)=(CountedRepairKeyScan.scratch Z hs).tape i ∧
      (cleaned q b Z hs data).head (Fin.natAdd 14 i)=(CountedRepairKeyScan.scratch Z hs).head i := by
  have hi : Fin.natAdd 14 i≠(10 : Fin 42) := by
    intro h
    have hv := congrArg Fin.val h
    change 14+i.val=10 at hv
    omega
  simp only [cleaned,setTape,Function.update_of_ne hi,CountedTapeRepairBank.input,CountedRepairScanPrepare.input,
    Tapes.append,Fin.addCases_right]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.CountedTapeRepairEndpoint
