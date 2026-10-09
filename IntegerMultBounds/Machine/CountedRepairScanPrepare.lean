import IntegerMultBounds.Machine.CountedRepairScanSeed
import IntegerMultBounds.Compact.KeyInstance

/-! Physical preparation of the complete fixed scan bank from a source stream,
original q/b/n descriptors, control word and otherwise blank workspace. -/
namespace IntegerMultBounds.Machine.CountedRepairScanPrepare
noncomputable section
open CountedRepairScanMetadataRun
open CountedRepairKeyScan (scratch)
open CountedRankSplitBank (placed_exact)

theorem selector_filled (k : ℕ) : filled (KeySelect.selector 0) 0 k true=KeySelect.selector k := by
  induction k with
  | zero => simp only [filled,List.replicate_zero,putWord]
  | succ k ih =>
    have h := putWord_append_forward (KeySelect.selector 0) 0 (List.replicate k (bitSymbol (a := 1) true)) [bitSymbol true]
    simp only [List.length_replicate,zero_add,putWord] at h
    rw [show putWord (KeySelect.selector 0) 0 (List.replicate k (bitSymbol (a := 1) true))=KeySelect.selector k from ih,UnarySelector.selector_succ] at h
    simpa only [filled,List.replicate_add,List.replicate_one] using h.symm

theorem ctr_filled (k : ℕ) : filled (RepairScan.ctrTape []) 1 k false=RepairScan.ctrTape (List.replicate k false) := by
  rw [IntegerMultBounds.Compact.PowerTwo.ctrTape_eq,IntegerMultBounds.Compact.PowerTwo.ctrTape_eq]
  simp only [filled,List.map_nil,putWord,List.map_replicate]

def place : Fin (12+30) ≃ Fin 42 where
  toFun := ![13,7,14,23,24,25,26,27,28,29,30,31,0,1,2,3,4,5,6,8,9,10,11,12,15,16,17,18,19,20,21,22,32,33,34,35,36,37,38,39,40,41]
  invFun := ![12,13,14,15,16,17,18,1,19,20,21,22,23,0,2,24,25,26,27,28,29,30,31,3,4,5,6,7,8,9,10,11,32,33,34,35,36,37,38,39,40,41]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bank (k : ℕ) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) : Tapes 42 1 :=
  (RepairScan.bank k [] 0 (fun _ => blank) 0 src 0 (FlagCopy.keyTape [])
    (RepairScan.ctrTape (List.replicate k false))).append (scratch Z hs)

def input (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) :=
  (CountedRepairScanSeed.input src).append (scratch Z hs)

def metadataProgram := Placement.placed CountedRepairScanMetadata.program place
def program := seq (extend CountedRepairScanSeed.program 28) metadataProgram

theorem active_bank (k : ℕ) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active place (bank k src Z hs)=CountedRankSplitBank.bank
      (RepairScan.ctrTape (List.replicate k false)) (KeySelect.selector k) (fun _ => blank) 1 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem place_extra (i : Fin 30) : place (Fin.natAdd 12 i)=(![0,1,2,3,4,5,6,8,9,10,11,12,15,16,17,18,19,20,21,22,32,33,34,35,36,37,38,39,40,41] : Fin 30 → Fin 42) i := by
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
      (fun v => v=bank (Z.length*q+Z.length*b) src Z hs)
      (1000*((Z.length+1)*(q+b+1))) := by
  have h := CountedRepairScanMetadataRun.runs (RepairScan.ctrTape []) (KeySelect.selector 0)
    (fun _ => blank) 1 0 0 hs q b Z.length hq hb hv hc
  rw [ctr_filled,selector_filled] at h
  have h1 := h.consequence (fun _ h => h) (fun _ h => h) (budget_linear Z.length q b)
  exact placed_exact place _ _ _ _ (active_bank 0 src Z hs) (active_bank _ src Z hs) (extra_bank _ src Z hs) h1

theorem runs (q b : ℕ) (hq : 0<q) (hb : 0<b) (src : ℤ → Fin 5) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=input src Z hs)
      (fun v => v=bank (Z.length*q+Z.length*b) src Z hs)
      (1004*((Z.length+1)*(q+b+1))) := by
  have h1 := hoare_extend_eq (CountedRepairScanSeed.runs src) (scratch Z hs)
  have h2 := metadata_runs q b hq hb src Z hs hv hc
  have hp : 1≤(Z.length+1)*(q+b+1) := by
    have hpos := Nat.mul_pos (by omega : 0<Z.length+1) (by omega : 0<q+b+1)
    omega
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRepairScanPrepare
