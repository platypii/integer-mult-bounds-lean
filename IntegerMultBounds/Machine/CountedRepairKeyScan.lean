import IntegerMultBounds.Machine.CountedRepairKeyValue

/-! The actual scan contract for the fixed repair-key machine on a forty-two
 tape bank: fourteen scan tapes and twenty-eight retained scratch tapes. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyScan
noncomputable section
open CountedRepairKeyBank
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo
open CountedRankSplitBank (placed_exact)

def payload (Z : List Bool) : Tapes 9 1 :=
  PackedInverse.input [] [] Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0

def scratch (Z : List Bool) (hs : Fin 3 → List Bool) : Tapes 28 1 :=
  (CountedPackedInverse.bank (payload Z) hs).append (⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 1)

def keyed (Z cs : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) : Tapes 30 1 :=
  bank (payload Z) hs cs (FlagCopy.keyTape key) (fun _ => blank) (fun _ => blank) 0 0 0

def place : Fin (30+12) ≃ Fin 42 where
  toFun := ![14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,13,12,40,41,0,1,2,3,4,5,6,7,8,9,10,11]
  invFun := ![30,31,32,33,34,35,36,37,38,39,40,41,27,26,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28,29]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def program := Placement.placed CountedRepairKeyRun.program place

theorem active_scan (k c j : ℕ) (records : List Partition.Record) (flag : ℕ → Bool) (bits : ℕ → List Bool)
    (Z : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) :
    Placement.active place ((RepairScan.scanBank k records flag bits c j key j).append (scratch Z hs)) =
      keyed Z (RepairScan.counter c j) hs key := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem place_extra (i : Fin 12) : place (Fin.natAdd 30 i) = Fin.castAdd 30 i := by
  fin_cases i <;> decide

theorem extra_bank (v : Tapes 11 1) (src ctr : ℤ → Fin 5) (p : ℤ) (S : Tapes 28 1)
    (K : ℤ → Fin 5) :
    Placement.extra place ((v.append (⟨(fun i => if i=0 then p else if i=1 then 0 else 1),(fun i => if i=0 then src else if i=1 then FlagCopy.keyTape [] else ctr)⟩ : Tapes 3 1)).append S) =
      Placement.extra place ((v.append (⟨(fun i => if i=0 then p else if i=1 then 0 else 1),(fun i => if i=0 then src else if i=1 then K else ctr)⟩ : Tapes 3 1)).append S) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals rw [place_extra]
  all_goals fin_cases i <;> rfl

theorem extra_scan (k c j : ℕ) (records : List Partition.Record) (flag : ℕ → Bool) (bits : ℕ → List Bool)
    (Z : List Bool) (hs : Fin 3 → List Bool) (key : List (Fin 5)) :
    Placement.extra place ((RepairScan.scanBank k records flag bits c j [] j).append (scratch Z hs)) =
      Placement.extra place ((RepairScan.scanBank k records flag bits c j key j).append (scratch Z hs)) := by
  unfold RepairScan.scanBank RepairScan.bank
  exact extra_bank _ _ _ _ _ _

theorem contract (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (records : List Partition.Record) (c : ℕ) (hlen : records.length≤Mi q b Z) (hcap : records.length≤2^c) :
    RepairScan.KeyContract (Z.length*q+Z.length*b) records
      (rankFlag (rankEquiv q b Z) (badSet q b Z))
      (rankKey (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (Z.length*q+Z.length*b))
      c 28 program (5100*((Z.length+1)*(q+b+1))) (scratch Z hs) := by
  intro j hj
  have hjM : j<Mi q b Z := lt_of_lt_of_le hj hlen
  have hcj : Counter.value (RepairScan.counter c j)=j := counter_value c j (lt_of_lt_of_le hj hcap)
  have h := CountedRepairKeyRun.runs q b hb (by omega) hbq Z (RepairScan.counter c j) hs hv hc
  have hflag := CountedRepairKeyValue.flag_rank q b hb hbq Z (RepairScan.counter c j) j hjM hcj
  have hbits := CountedRepairKeyValue.bits_rank q b hb (by omega) Z (RepairScan.counter c j) j hjM hcj
  have hout : CountedRepairKeyRun.output q b hb (by omega) (V q Z (RepairScan.counter c j))
      (W q b Z (RepairScan.counter c j)) Z (RepairScan.counter c j) hs =
      keyed Z (RepairScan.counter c j) hs (FlagCopy.keyWord
        (rankFlag (rankEquiv q b Z) (badSet q b Z) j)
        (rankKey (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (Z.length*q+Z.length*b) j)) := by
    unfold CountedRepairKeyRun.output
    rw [hflag,hbits]
    rfl
  rw [hout] at h
  exact placed_exact place _ _ _ _ (active_scan _ _ _ _ _ _ _ _ [])
    (active_scan _ _ _ _ _ _ _ _ _) (extra_scan _ _ _ _ _ _ _ _ _) h

end
end IntegerMultBounds.Machine.CountedRepairKeyScan
