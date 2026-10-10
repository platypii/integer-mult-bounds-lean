import IntegerMultBounds.Machine.CompactComplexSpectatorTargetFamily
import IntegerMultBounds.Machine.CompactComplexSpectatorRoleSchedule

/-! The genuine spectator promoter acts on the stopped caller's permanent
controller/native65/role bank. True denominator slots stay in existing
storage; the retained original scalar43 suffix remains beyond that storage.
No tape indices are inserted ahead of the existing recursive ledgers. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorTargetBank
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexControllerNativeFrame
open NativeSignedGapPromoteReturn (word)
open NativeSignedReturnStream (volume)
open RadixSignedShiftRight (Word)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def roleSlot (j : Fin c) : Fin (permanentTapes s c) :=
  CompactComplexNativeRoleBridge.roleSlot (s:=s+43) j
def oldSlot (j : Fin s) : Fin (permanentTapes s c) :=
  Fin.castAdd c (storageSlot (Fin.castAdd 43 j))
def numericSlot (j : Fin 66) : Fin (permanentTapes s c) :=
  Fin.castAdd c (nativeSlot (s:=s+43) j)

theorem role_injective : Function.Injective (roleSlot (s:=s) (c:=c)) := by
  intro i j h
  exact Fin.natAdd_injective _ _ h

def ports (cur tar : Fin s) (len : Fin 66) (j : Fin c) :=
  CompactComplexSpectatorTargetFamily.common (roleSlot j) (oldSlot cur) (oldSlot tar) (numericSlot len)

theorem ports_injective (cur tar : Fin s) (hne : cur≠tar) (len : Fin 66) (j : Fin c) :
    Function.Injective (ports cur tar len j) := by
  intro i k h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hc := cur.isLt
  have ht := tar.isLt
  have hl := len.isLt
  have hval : cur.val≠tar.val := fun he => hne (Fin.ext he)
  fin_cases i <;> fin_cases k <;>
    simp [ports,CompactComplexSpectatorTargetFamily.common,roleSlot,oldSlot,numericSlot,
      CompactComplexNativeRoleBridge.roleSlot,storageSlot,nativeSlot,tapes,
      Fin.val_natAdd,Fin.val_castAdd] at hv ⊢
  all_goals omega

theorem old_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (j : Fin s) :
    (bank control queue scalar stage tail storage payload).head (oldSlot j)=storage.head j ∧
      (bank control queue scalar stage tail storage payload).tape (oldSlot j)=storage.tape j := by
  simp only [oldSlot,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,storageSlot,Tapes.append,
    Fin.addCases_left,Fin.addCases_right,and_self]

theorem role_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (j : Fin c) :
    (bank control queue scalar stage tail storage payload).head (roleSlot j)=payload.head (Fin.natAdd 1 j) ∧
      (bank control queue scalar stage tail storage payload).tape (roleSlot j)=payload.tape (Fin.natAdd 1 j) := by
  have he : (⟨j.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 j := Fin.ext (by simp;omega)
  simp only [roleSlot,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexNativeRoleBridge.roleSlot,Tapes.append,Fin.addCases_right,
    CompactNativeRoleSourcePorts.roles,he,and_self]

theorem bank_execute (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (words : Fin c → ℤ → Fin 6) (js : List (Fin c)) :
    CompactComplexSpectatorPromoteFamily.execute roleSlot words js
      (bank control queue scalar stage tail storage payload) =
      bank control queue scalar stage tail storage
        (CompactComplexSpectatorRoleSchedule.execute words js payload) := by
  induction js generalizing payload with
  | nil => rfl
  | cons j js ih =>
    simp only [CompactComplexSpectatorPromoteFamily.execute,
      CompactComplexSpectatorRoleSchedule.execute]
    have he := CompactComplexStoppedCodecCaller.bank_setRole control queue scalar stage tail storage payload j (words j)
    exact (congrArg (CompactComplexSpectatorPromoteFamily.execute roleSlot words js) he.symm).trans (ih _)

/-- The actual permanent-bank family excludes the completed selected role,
reads old live and generated target denominators, and returns every controller,
native header, immutable scalar and existing stack exactly where it began. -/
theorem spectators_runs (cur tar : Fin s) (hne : cur≠tar) (len : Fin 66) (selected : Fin c)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+c) 2) (ws : Fin c → List Word)
    (current target V : ℕ) (hle : current≤target) (ls : List Bool)
    (hd : ∀ j w,w∈ws j → target-current≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hlen : Counter.value ls=V)
    (hcanonical : GrowingCounterData.Canonical ls)
    (hcurrent : (bank control queue scalar stage tail storage payload).head (oldSlot cur)=1 ∧
      (bank control queue scalar stage tail storage payload).tape (oldSlot cur)=
        RadixZeroFill.encodedBinary (bits current))
    (htarget : (bank control queue scalar stage tail storage payload).head (oldSlot tar)=1 ∧
      (bank control queue scalar stage tail storage payload).tape (oldSlot tar)=
        RadixZeroFill.encodedBinary (bits target))
    (hlength : (bank control queue scalar stage tail storage payload).head (numericSlot len)=1 ∧
      (bank control queue scalar stage tail storage payload).tape (numericSlot len)=RadixZeroFill.encodedBinary ls)
    (hsource : ∀ j,j≠selected →
      (bank control queue scalar stage tail storage payload).head (roleSlot j)=0 ∧
      (bank control queue scalar stage tail storage payload).tape (roleSlot j)=word (ws j)) :
    HoareTime (CompactComplexSpectatorTargetFamily.compile roleSlot (oldSlot cur) (oldSlot tar) (numericSlot len)
      (ports_injective cur tar hne len) (CompactComplexSpectatorPromoteFamily.spectatorList selected)).2
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar stage tail storage payload))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar stage tail storage
          (CompactComplexSpectatorRoleSchedule.execute
            (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result (target-current))))
              (CompactComplexSpectatorPromoteFamily.spectatorList selected) payload)))
      ((CompactComplexSpectatorPromoteFamily.spectatorList selected).length*(130*V+8*target+360)) := by
  have h := CompactComplexSpectatorTargetFamily.spectators_runs roleSlot role_injective
    (oldSlot cur) (oldSlot tar) (numericSlot len) (ports_injective cur tar hne len)
    selected ws (bank control queue scalar stage tail storage payload) current target V hle ls
    hd hn hv hlen hcanonical hcurrent htarget hlength hsource
  rw [bank_execute] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSpectatorTargetBank
