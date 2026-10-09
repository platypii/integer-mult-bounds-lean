import IntegerMultBounds.Machine.CountedLateRepairMetadata
import IntegerMultBounds.Machine.CountedLateRepairScanBank
import IntegerMultBounds.Machine.CountedRepairScanPrepare

/-! Physical preparation of the complete fixed scan bank from a source stream,
original q/b/n descriptors, control word and otherwise blank workspace. -/
namespace IntegerMultBounds.Machine.CountedLateRepairPrepare
noncomputable section
open CountedRepairScanMetadataRun (filled)
open CountedLateRepairMetadata (budget_linear)
open CountedLateRepairScanBank (scratch)
open CountedRankSplitBank (placed_exact)

open CountedRepairScanPrepare (selector_filled ctr_filled)

def place : Fin (12+34) ≃ Fin 46 where
  toFun := ![13,7,14,25,26,27,28,29,30,31,32,33,0,1,2,3,4,5,6,8,9,10,11,12,15,16,17,18,19,20,21,22,23,24,34,35,36,37,38,39,40,41,42,43,44,45]
  invFun := ![12,13,14,15,16,17,18,1,19,20,21,22,23,0,2,24,25,26,27,28,29,30,31,32,33,3,4,5,6,7,8,9,10,11,34,35,36,37,38,39,40,41,42,43,44,45]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bank (k : ℕ) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) : Tapes 46 1 :=
  (RepairScan.bank k [] 0 (fun _ => blank) 0 src 0 (FlagCopy.keyTape [])
    (RepairScan.ctrTape (List.replicate k false))).append (scratch Z hs)

def input (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) :=
  (CountedRepairScanSeed.input src).append (scratch Z hs)

def metadataProgram := Placement.placed CountedLateRepairMetadata.program place
def program := seq (extend CountedRepairScanSeed.program 32) metadataProgram

theorem active_bank (k : ℕ) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active place (bank k src Z hs)=CountedRankSplitBank.bank
      (RepairScan.ctrTape (List.replicate k false)) (KeySelect.selector k) (fun _ => blank) 1 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem place_extra (i : Fin 34) : place (Fin.natAdd 12 i)=(![0,1,2,3,4,5,6,8,9,10,11,12,15,16,17,18,19,20,21,22,23,24,34,35,36,37,38,39,40,41,42,43,44,45] : Fin 34 → Fin 46) i := by
  fin_cases i <;> decide

theorem extra_bank (k : ℕ) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra place (bank 0 src Z hs)=Placement.extra place (bank k src Z hs) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals rw [place_extra]
  all_goals fin_cases i <;> rfl

theorem metadata_runs (q b : ℕ) (hq : 0<q) (hb : 0<b) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime metadataProgram (fun v => v=bank 0 src Z hs)
      (fun v => v=bank (Z.length*q+Z.length*b+Z.length*b) src Z hs)
      (2000*((Z.length+1)*(q+b+1))) := by
  have h := CountedLateRepairMetadata.runs (RepairScan.ctrTape []) (KeySelect.selector 0)
    (fun _ => blank) 1 0 0 hs q b Z.length hq hb hv hc
  rw [ctr_filled,selector_filled] at h
  have h1 := h.consequence (fun _ h => h) (fun _ h => h) (budget_linear Z.length q b)
  exact placed_exact place _ _ _ _ (active_bank 0 src Z hs) (active_bank _ src Z hs) (extra_bank _ src Z hs) h1

theorem runs (q b : ℕ) (hq : 0<q) (hb : 0<b) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=input src Z hs)
      (fun v => v=bank (Z.length*q+Z.length*b+Z.length*b) src Z hs)
      (2004*((Z.length+1)*(q+b+1))) := by
  have h1 := hoare_extend_eq (CountedRepairScanSeed.runs src) (scratch Z hs)
  have h2 := metadata_runs q b hq hb src Z hs hv hc
  have hp : 1≤(Z.length+1)*(q+b+1) := by
    have hpos := Nat.mul_pos (by omega : 0<Z.length+1) (by omega : 0<q+b+1)
    omega
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedLateRepairPrepare
