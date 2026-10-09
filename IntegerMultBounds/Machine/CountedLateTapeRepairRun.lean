import IntegerMultBounds.Machine.CountedLateTapeRepairBank
import IntegerMultBounds.Machine.CountedLateRepairScan

/-! The same finite machine repairs every admissible runtime q/b/n instance,
starting without supplied sort width, zero counter, sentinels or constants. -/
namespace IntegerMultBounds.Machine.CountedLateTapeRepairRun
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo
open CountedLateTapeRepairBank

def scanProgram := RepairScan.program 32 CountedLateRepairScan.program
def program := seq CountedLateRepairPrepare.program scanProgram

theorem prepared_scan (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    (RepairScan.scanBank (width q b Z) (records q b Z data)
      (rankFlag (lateRankEquiv q b Z) (lateBadSet q b Z))
      (rankKey (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z) (width q b Z))
      (width q b Z) 0 [] 0).append (CountedLateRepairScanBank.scratch Z hs)=prepared q b Z hs data := by
  rw [RepairScan.scanBank_zero]
  rfl

theorem scan_runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (data : Address q b Z → List Bool) :
    HoareTime scanProgram (fun v => v=prepared q b Z hs data) (fun v => v=output q b Z hs data)
      (scanCost q b Z data) := by
  have hlen : (records q b Z data).length=lateMi q b Z := plain_length _ _
  have hcap := capacity q b Z (by omega)
  have hK := CountedLateRepairScan.contract q b hb hbq Z hs hv hc (records q b Z data)
    (width q b Z) hlen.le (by simpa only [hlen,width] using hcap)
  have h := tape_repair (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z) (lateBadSet q b Z)
    (width q b Z) (CountedLateTapeRepairBank.ideal_preserves q b Z) (CountedLateTapeRepairBank.program_agrees q b Z) hcap data (width q b Z) 32
    CountedLateRepairScan.program (keyCost q b Z) (CountedLateRepairScanBank.scratch Z hs) hK
  have he := prepared_scan q b Z hs data
  dsimp only [records] at he
  rw [he] at h
  exact h

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (data : Address q b Z → List Bool) :
    HoareTime program (fun v => v=CountedLateTapeRepairBank.input q b Z hs data) (fun v => v=output q b Z hs data)
      (cost q b Z data) := by
  have h1 := CountedLateRepairPrepare.runs q b (by omega) (by omega)
    (RepairScan.srcTape (records q b Z data)) Z hs hv hc
  have h2 := scan_runs q b hb hbq Z hs hv hc data
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost volume; omega)

end
end IntegerMultBounds.Machine.CountedLateTapeRepairRun
