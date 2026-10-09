import IntegerMultBounds.Machine.ActiveRepairLateFieldsCopy
import IntegerMultBounds.Machine.CountedLateRepairToggle

/-! Later extracted-field repair retains original V/T/Z/current controls,
q/b/n and the full scan counter. All working copies are produced physically. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsBank
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def originals (V W U cs : List Bool) : Tapes 4 1 :=
  ⟨![0,0,0,1],![word V,word W,word U,RepairScan.ctrTape cs]⟩

def bank (v : Tapes 30 1) (T V W U cs : List Bool) : Tapes 35 1 :=
  (v.append (FiniteReturnStack.bank (word T) 0)).append (originals V W U cs)

def before (V W U X cs : List Bool) (hs : Fin 3 → List Bool) : Tapes 35 1 :=
  bank (CountedLateRepairGuard.before [] [] [] X hs) [] V W U cs

def copiedV (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  WordBankCleanup.write (before V W U X cs hs) 0 (word V)
def copiedW (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  WordBankCleanup.write (copiedV V W U X cs hs) 1 (word W)
def loaded (V W U X cs : List Bool) (hs : Fin 3 → List Bool) : Tapes 35 1 :=
  bank (CountedLateRepairGuard.before V W U X hs) [] V W U cs

theorem copied_eq (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    WordBankCleanup.write (copiedW V W U X cs hs) 2 (word U)=loaded V W U X cs hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def inverted (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (CountedLateRepairPrefix.output q b hb hbq V W U X hs) [] V W U cs

def toggled (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  (CountedLateRepairToggle.after q b hb hbq V W U X hs).append (originals V W U cs)

theorem toggle_input (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    inverted q b hb hbq V W U X cs hs=
      (CountedLateRepairToggle.before q b hb hbq V W U X hs).append (originals V W U cs) := rfl

def copyVProgram := ActiveRepairLateFieldsCopy.program (31 : Fin 35) 0 (by decide) (by decide)
def copyWProgram := ActiveRepairLateFieldsCopy.program (32 : Fin 35) 1 (by decide) (by decide)
def copyUProgram := ActiveRepairLateFieldsCopy.program (33 : Fin 35) 2 (by decide) (by decide)
def copyProgram := seq (seq copyVProgram copyWProgram) copyUProgram
def inverseProgram := extend (CountedLateRepairPrefix.program (a := 1)) 5
def toggleProgram := extend CountedLateRepairToggle.program 4

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsBank
