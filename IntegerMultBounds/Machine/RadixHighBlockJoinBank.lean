import IntegerMultBounds.Machine.RadixDigitMoveBlockExecution
import IntegerMultBounds.Machine.FixedBaseDescriptorQuotient
import IntegerMultBounds.Machine.FixedBasePowerStep

/-! Shared exact bank for ordered high-block join/separate bodies and their
independent physical setup/cleanup. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinBank
noncomputable section
variable {q a : ℕ}

def count (q : ℕ) := ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4)+16
theorem count_eq (q : ℕ) : count q = 2*q+34 := by unfold count RadixDigitMoveCore.count; omega
private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => CountedLoopReuseAlphabet.binary bs

def prefixSlot : Fin (count q) := ⟨q+4,by unfold count RadixDigitMoveCore.count; omega⟩
def suffixSlot : Fin (count q) := ⟨q+5,by unfold count RadixDigitMoveCore.count; omega⟩
def spectatorSlot : Fin (count q) := ⟨2*q+14,by unfold count RadixDigitMoveCore.count; omega⟩
def baseSlot : Fin (count q) := ⟨2*q+31,by unfold count RadixDigitMoveCore.count; omega⟩
def originalPrefixSlot : Fin (count q) := ⟨2*q+32,by unfold count RadixDigitMoveCore.count; omega⟩
def originalSuffixSlot : Fin (count q) := ⟨2*q+33,by unfold count RadixDigitMoveCore.count; omega⟩
def scratchSlot (i : Fin 13) : Fin (count q) := ⟨2*q+18+i.val,by unfold count RadixDigitMoveCore.count; omega⟩

/-- Digit bank first2q+18;13scratch;fixedq;retained originalP/E.
S is the digit bank's retained spectator header. No outer clock is embedded. -/
def bank (source : ℤ → Fin (a+4)) (ss originalP originalE : List Bool)
    (ps es ws : Option (List Bool)) : Tapes (count q) a :=
  ⟨(fun i => if i.val = (prefixSlot (q := q)).val then hd ps else if i.val = (suffixSlot (q := q)).val then hd es
      else if i.val = (baseSlot (q := q)).val then hd ws else if i.val = (spectatorSlot (q := q)).val ∨ i.val = (originalPrefixSlot (q := q)).val ∨ i.val = (originalSuffixSlot (q := q)).val then 1 else 0),
    (fun i => if i.val = 0 then source else if i.val = (prefixSlot (q := q)).val then tp ps else if i.val = (suffixSlot (q := q)).val then tp es
      else if i.val = (baseSlot (q := q)).val then tp ws else if i.val = (spectatorSlot (q := q)).val then CountedLoopReuseAlphabet.binary ss
      else if i.val = (originalPrefixSlot (q := q)).val then CountedLoopReuseAlphabet.binary originalP
      else if i.val = (originalSuffixSlot (q := q)).val then CountedLoopReuseAlphabet.binary originalE else fun _ => blank)⟩

/-- Literal initialized arithmetic tail; the13work tapes are whollyblank. -/
def tail (ws originalP originalE : List Bool) : Tapes 16 a :=
  ⟨(fun i => if i.val = 13 ∨ i.val = 14 ∨ i.val = 15 then 1 else 0),
    (fun i => match i.val with
      | 13 => CountedLoopReuseAlphabet.binary ws
      | 14 => CountedLoopReuseAlphabet.binary originalP
      | 15 => CountedLoopReuseAlphabet.binary originalE
      | _ => fun _ => blank)⟩

end
end IntegerMultBounds.Machine.RadixHighBlockJoinBank
