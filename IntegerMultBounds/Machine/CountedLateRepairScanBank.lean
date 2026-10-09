import IntegerMultBounds.Machine.CountedLateRepairKeyRun

/-! The fixed later repair scan bank: fourteen scan tapes and thirty-two
retained scratch tapes, with the actual key machine placed on thirty-four. -/
namespace IntegerMultBounds.Machine.CountedLateRepairScanBank
noncomputable section

def scratch (X : List Bool) (hs : Fin 3 → List Bool) : Tapes 32 1 :=
  ((CountedPackedLateRun.bank [] [] [] X [] (fun _ => blank) (fun _ => blank)
    (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append (FixedHeaderBankCopy.empty 2)).append
      (FixedHeaderBankCopy.empty 2)

def keyed (X cs : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) :=
  CountedLateRepairKeyBank.bank [] [] [] X [] [] hs cs (fun _ => blank) (FlagCopy.keyTape key) 0 0

def place : Fin (34+12) ≃ Fin 46 where
  toFun := ![14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,13,12,44,45,0,1,2,3,4,5,6,7,8,9,10,11]
  invFun := ![34,35,36,37,38,39,40,41,42,43,44,45,31,30,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,32,33]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def program := Placement.placed CountedLateRepairKeyRun.program place

theorem active_scan (k c j : ℕ) (records : List Partition.Record) (flag : ℕ → Bool)
    (bits : ℕ → List Bool) (X : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) :
    Placement.active place ((RepairScan.scanBank k records flag bits c j key j).append (scratch X hs))=
      keyed X (RepairScan.counter c j) hs key := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem place_extra (i : Fin 12) : place (Fin.natAdd 34 i)=Fin.castAdd 34 i := by
  fin_cases i <;> decide

theorem extra_bank (v : Tapes 11 1) (src ctr : ℤ → Fin 5) (p : ℤ) (S : Tapes 32 1)
    (K : ℤ → Fin 5) :
    Placement.extra place ((v.append (⟨(fun i => if i=0 then p else if i=1 then 0 else 1),
      (fun i => if i=0 then src else if i=1 then FlagCopy.keyTape [] else ctr)⟩ : Tapes 3 1)).append S)=
    Placement.extra place ((v.append (⟨(fun i => if i=0 then p else if i=1 then 0 else 1),
      (fun i => if i=0 then src else if i=1 then K else ctr)⟩ : Tapes 3 1)).append S) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals rw [place_extra]
  all_goals fin_cases i <;> rfl

theorem extra_scan (k c j : ℕ) (records : List Partition.Record) (flag : ℕ → Bool)
    (bits : ℕ → List Bool) (X : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) :
    Placement.extra place ((RepairScan.scanBank k records flag bits c j [] j).append (scratch X hs))=
      Placement.extra place ((RepairScan.scanBank k records flag bits c j key j).append (scratch X hs)) := by
  unfold RepairScan.scanBank RepairScan.bank
  exact extra_bank _ _ _ _ _ _

end
end IntegerMultBounds.Machine.CountedLateRepairScanBank
