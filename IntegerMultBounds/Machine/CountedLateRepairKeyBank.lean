import IntegerMultBounds.Machine.CountedLateRepairToggle
import IntegerMultBounds.Machine.CountedLateRepairConcat

/-! Fixed34 common bank for later destination keys. The three rank words,
original controls and headers, exception flag and literal destination words
share recycled blank arithmetic workspace. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyBank
noncomputable section
open CountedGuardGadgetRecord (word)

def bank (V W U X T D : List Bool) (hs : Fin 3 → List Bool) (cs : List Bool)
    (F K : ℤ → Fin 5) (pf pk : ℤ) : Tapes 34 1 :=
  ((CountedPackedLateRun.bank V W U X [] (fun _ => blank) (fun _ => blank)
    (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append
      (⟨![pf,0],![F,fun _ => blank]⟩ : Tapes 2 1)).append
      (⟨![1,pk,0,0],![RepairScan.ctrTape cs,K,word T,word D]⟩ : Tapes 4 1)

def initial (X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank [] [] [] X [] [] hs cs (fun _ => blank) (FlagCopy.keyTape []) 0 0

def ranked (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank V W U X [] [] hs cs (fun _ => blank) (FlagCopy.keyTape []) 0 0

def fl (q b : ℕ) (V W U X : List Bool) :=
  CountedLateRepairGuard.flag q b V W X || CountedLateRepairGuard.flag q b V U X

def inverted (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X [] [] hs cs (CountedLateRepairFlag.key (fl q b V W U X)) (FlagCopy.keyTape []) 1 0

def target (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W U X : List Bool) :=
  CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U X) X

def toggled (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X (target q b hb hbq V W U X) [] hs cs
    (CountedLateRepairFlag.key (fl q b V W U X)) (FlagCopy.keyTape []) 1 0

def dirty (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W U X : List Bool) :=
  CountedLateRepairInverse.temp q b hb hbq V W U X ++ CountedLateRepairInverse.restored b hb U X

def concatenated (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X (target q b hb hbq V W U X) (dirty q b hb hbq V W U X) hs cs
    (CountedLateRepairFlag.key (fl q b V W U X)) (FlagCopy.keyTape []) 1 0

def bits (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W U X : List Bool) :=
  target q b hb hbq V W U X ++ dirty q b hb hbq V W U X

def written (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X (target q b hb hbq V W U X) (dirty q b hb hbq V W U X) hs cs
    (CountedLateRepairFlag.key (fl q b V W U X))
    (FlagCopy.keyTape (FlagCopy.keyWord (fl q b V W U X) (bits q b hb hbq V W U X))) 0 0

def prefixPlace : Fin (30+4) ≃ Fin 34 where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def togglePlace : Fin (31+3) ≃ Fin 34 where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,32,30,31,33]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,31,32,30,33]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def concatPlace : Fin (4+30) ≃ Fin 34 where
  toFun := ![29,33,1,2,0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31,32]
  invFun := ![4,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,0,31,32,33,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def writePlace : Fin (4+30) ≃ Fin 34 where
  toFun := ![28,31,32,33,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,29,30]
  invFun := ![4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,0,32,33,1,2,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def prefixProgram := extend (CountedLateRepairPrefix.program (a := 1)) 4
def toggleProgram := Placement.placed CountedLateRepairToggle.program togglePlace
def concatProgram := Placement.placed CountedLateRepairConcat.program concatPlace
def writeProgram := Placement.placed CountedRepairKeyAppend.program writePlace

end
end IntegerMultBounds.Machine.CountedLateRepairKeyBank
