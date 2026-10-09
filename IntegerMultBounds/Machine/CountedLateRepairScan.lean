import IntegerMultBounds.Machine.CountedLateRepairKeyValue
import IntegerMultBounds.Machine.CountedLateRepairScanBank

/-! Exact scan key contract for the actual original-header later key machine. -/
namespace IntegerMultBounds.Machine.CountedLateRepairScan
noncomputable section
open CountedLateRepairScanBank
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo
open CountedRankSplitBank (placed_exact)

def program := CountedLateRepairScanBank.program

theorem contract (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (records : List Partition.Record) (c : ℕ) (hlen : records.length≤lateMi q b Z) (hcap : records.length≤2^c) :
    RepairScan.KeyContract (Z.length*q+Z.length*b+Z.length*b) records
      (rankFlag (lateRankEquiv q b Z) (lateBadSet q b Z))
      (rankKey (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z) (Z.length*q+Z.length*b+Z.length*b))
      c 32 program (10300*((Z.length+1)*(q+b+1))) (scratch Z hs) := by
  intro j hj
  have hjM : j<lateMi q b Z := lt_of_lt_of_le hj hlen
  have hcj : Counter.value (RepairScan.counter c j)=j := counter_value c j (lt_of_lt_of_le hj hcap)
  have h := CountedLateRepairKeyRun.runs q b hb (by omega) hbq Z (RepairScan.counter c j) hs hv hc
  have hflag := CountedLateRepairKeyValue.flag_rank q b hb hbq Z (RepairScan.counter c j) j hjM hcj
  have hbits := CountedLateRepairKeyValue.bits_rank q b hb (by omega) Z (RepairScan.counter c j) j hjM hcj
  have hout : CountedLateRepairKeyRun.output q b hb (by omega) Z (RepairScan.counter c j) hs =
      keyed Z (RepairScan.counter c j) hs (FlagCopy.keyWord
        (rankFlag (lateRankEquiv q b Z) (lateBadSet q b Z) j)
        (rankKey (lateRankEquiv q b Z) (lateSperm q b Z) (lateTperm q b Z)
          (Z.length*q+Z.length*b+Z.length*b) j)) := by
    unfold CountedLateRepairKeyRun.output CountedLateRepairKeyCleanup.output keyed
    rw [hflag,hbits]
  rw [hout] at h
  exact placed_exact place _ _ _ _ (active_scan _ _ _ _ _ _ _ _ [])
    (active_scan _ _ _ _ _ _ _ _ _) (extra_scan _ _ _ _ _ _ _ _ _) h

end
end IntegerMultBounds.Machine.CountedLateRepairScan
