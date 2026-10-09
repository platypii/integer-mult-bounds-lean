import IntegerMultBounds.Machine.CountedRankSplitEndpoint
import IntegerMultBounds.Machine.CountedPackedInverse
import IntegerMultBounds.Machine.CountedGuardOriginal
import IntegerMultBounds.Machine.CountedIdealToggle

/-! Fixed extracted-field repair bank. Original V/T/current source controls,
q/b/n and the full scan counter are retained. Inverse, guard and toggle share
blank workspace; no prepared key sentinel or local rank is required. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyFieldsBank
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def bank (payload : Tapes 9 1) (hs : Fin 3 → List Bool) (cs : List Bool)
    (K F T : ℤ → Fin 5) (pk pf pt : ℤ) : Tapes 30 1 :=
  (CountedPackedInverse.bank payload hs).append
    (⟨![1,pk,pf,pt],![RepairScan.ctrTape cs,K,F,T]⟩ : Tapes 4 1)

def before (V W Z cs : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 1 :=
  bank (PackedInverse.input V W Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0)
    hs cs (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0

def inversePayload (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z : List Bool) : Tapes 9 1 :=
  PackedInverse.output q b hb hbq V W Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0

def inverted (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (inversePayload q b hb hbq V W Z) hs cs (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0

def flag (q b : ℕ) (V W Z : List Bool) :=
  (CountedGuardGadget.flags q b Z.length V W (CountedGuardConstantsData.c1 q b)
    (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b)).any id

def guarded (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (inversePayload q b hb hbq V W Z) hs cs (fun _ => blank)
    (CountedGuardGadgetFinish.key (CountedGuardGadget.flags q b Z.length V W
      (CountedGuardConstantsData.c1 q b) (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b)))
    (fun _ => blank) 0 1 0

def toggled (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  setTape (guarded q b hb hbq V W Z cs hs) 29
    (word (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)) 0

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

def inverseProgram := extend (CountedPackedInverse.program 1) 4
def guardProgram := Placement.placed (CountedGuardOriginal.program (a := 1)) guardPlace
def toggleProgram := Placement.placed (CountedIdealToggle.program 1) togglePlace

end
end IntegerMultBounds.Machine.ActiveRepairEarlyFieldsBank
