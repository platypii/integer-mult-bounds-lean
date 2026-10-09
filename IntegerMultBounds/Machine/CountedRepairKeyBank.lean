import IntegerMultBounds.Machine.CountedRankSplitEndpoint
import IntegerMultBounds.Machine.CountedPackedInverse
import IntegerMultBounds.Machine.CountedGuardOriginal
import IntegerMultBounds.Machine.CountedIdealToggle

/-! A fixed thirty-tape repair-key bank. The original scan counter, control and
q/b/n headers are retained; inverse, guard and toggle share blank workspace. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyBank
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def V (q : ℕ) (Z cs : List Bool) := Gather.field cs 0 (Z.length*q)
def W (q b : ℕ) (Z cs : List Bool) := Gather.field cs (Z.length*q) (Z.length*b)

def bank (payload : Tapes 9 1) (hs : Fin 3 → List Bool) (cs : List Bool)
    (K F T : ℤ → Fin 5) (pk pf pt : ℤ) : Tapes 30 1 :=
  (CountedPackedInverse.bank payload hs).append
    (⟨![1,pk,pf,pt],![RepairScan.ctrTape cs,K,F,T]⟩ : Tapes 4 1)

def before (V W Z cs : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 1 :=
  bank (PackedInverse.input V W Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0)
    hs cs (FlagCopy.keyTape []) (fun _ => blank) (fun _ => blank) 0 0 0

def input (Z cs : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 1 := before [] [] Z cs hs

def split (q b : ℕ) (Z cs : List Bool) (hs : Fin 3 → List Bool) := before (V q Z cs) (W q b Z cs) Z cs hs

def inversePayload (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z : List Bool) : Tapes 9 1 :=
  PackedInverse.output q b hb hbq V W Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0

def inverted (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (inversePayload q b hb hbq V W Z) hs cs (FlagCopy.keyTape []) (fun _ => blank) (fun _ => blank) 0 0 0

def flag (q b : ℕ) (V W Z : List Bool) :=
  (CountedGuardGadget.flags q b Z.length V W (CountedGuardConstantsData.c1 q b)
    (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b)).any id

def guarded (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (inversePayload q b hb hbq V W Z) hs cs (FlagCopy.keyTape [])
    (CountedGuardGadgetFinish.key (CountedGuardGadget.flags q b Z.length V W
      (CountedGuardConstantsData.c1 q b) (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b)))
    (fun _ => blank) 0 1 0

def toggled (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  setTape (guarded q b hb hbq V W Z cs hs) 29
    (word (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)) 0

def rankPlace : Fin (12+18) ≃ Fin 30 where
  toFun := ![26,0,1,9,10,11,12,13,14,15,16,17,2,3,4,5,6,7,8,18,19,20,21,22,23,24,25,27,28,29]
  invFun := ![1,2,12,13,14,15,16,17,18,3,4,5,6,7,8,9,10,11,19,20,21,22,23,24,25,26,0,27,28,29]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def guardPlace : Fin (15+15) ≃ Fin 30 where
  toFun := ![0,1,12,13,14,15,16,17,18,10,19,20,11,9,28,2,3,4,5,6,7,8,21,22,23,24,25,26,27,29]
  invFun := ![0,1,15,16,17,18,19,20,21,13,9,12,2,3,4,5,6,7,8,10,11,22,23,24,25,26,27,28,14,29]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def togglePlace : Fin (22+8) ≃ Fin 30 where
  toFun := ![6,2,7,8,29,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,0,1,3,4,5,26,27,28]
  invFun := ![22,23,1,24,25,26,0,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,27,28,29,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def rankProgram := Placement.placed (CountedRankSplitRun.program (a := 1)) rankPlace
def inverseProgram := extend (CountedPackedInverse.program 1) 4
def guardProgram := Placement.placed (CountedGuardOriginal.program (a := 1)) guardPlace
def toggleProgram := Placement.placed (CountedIdealToggle.program 1) togglePlace

end
end IntegerMultBounds.Machine.CountedRepairKeyBank
