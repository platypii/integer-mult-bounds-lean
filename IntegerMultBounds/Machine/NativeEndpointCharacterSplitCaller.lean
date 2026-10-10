import IntegerMultBounds.Machine.CompactComplexNonleafRoleSplit
import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore

namespace IntegerMultBounds.Machine.NativeEndpointCharacterSplitCaller
noncomputable section
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
variable {s c : ℕ}

def caller (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Tapes (CompactComplexNonleafRoleSplit.tapes s c) 2 :=
  (bank control queue scalar raw tail storage payload).append (aux.append (SharedBank.empty 7 2))

private theorem slot_header (i : Fin 43) :
    CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) (Fin.castAdd _ i)=
      Fin.castAdd 9 (CompactComplexNativeCodecFrame.headerSlot i) := by
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

private theorem slot_payload (i : Fin (1+c)) :
    CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) (Fin.natAdd 43 (Fin.castAdd 7 i))=
      if h : i.val=0 then Fin.castAdd 9 (CompactComplexNativeRoleBridge.sourceSlot (s:=s+43))
      else Fin.castAdd 9 (CompactComplexNativeRoleBridge.roleSlot (s:=s+43)
        ⟨i.val-1,by have := i.isLt; omega⟩) := by
  apply Fin.ext
  simp only [CompactComplexNonleafRoleSplit.slot,Fin.val_natAdd,Fin.val_castAdd]
  split_ifs <;> simp only [CompactComplexNativeRoleBridge.sourceSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd]
  all_goals have := i.isLt; omega

private theorem slot_work (i : Fin 7) :
    CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) (Fin.natAdd 43 (Fin.natAdd (1+c) i))=
      Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) (Fin.natAdd 2 i) := by
  apply Fin.ext
  simp only [CompactComplexNonleafRoleSplit.slot,Fin.val_natAdd]
  simp only [CompactComplexNonleafRoleEntry.tapes]
  split_ifs <;> omega

private theorem blank_raw (payload : Tapes (1+c) 2) :
    CompactNativeRoleInstall.blankRaw payload=payload.append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [Tapes.append,SharedBank.empty,Fin.addCases]
  all_goals split_ifs <;> first | rfl | omega

theorem active_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleSplit.placement
      (caller control queue scalar raw tail storage payload aux)=
      CompactNativeRoleOriginal.bank raw payload := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  unfold CompactNativeRoleOriginal.bank
  rw [blank_raw]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=43) (n:=(1+c)+7) with
  | left i =>
    simp only [slot_header,caller,bank,CompactComplexNativeRoleBridge.bank,
      CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
      Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    induction i using Fin.addCases (m:=1+c) (n:=7) with
    | right i =>
      simp only [slot_work,caller,Tapes.append,Fin.addCases_right,
        SharedBank.empty]
    | left i =>
      rw [slot_payload]
      simp only [caller,bank,CompactComplexNativeRoleBridge.bank,
        CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
        CompactComplexNativeRoleBridge.sourceSlot,CompactComplexNativeRoleBridge.roleSlot,
        CompactComplexControllerNativeFrame.nativeSlot,Tapes.append,Fin.addCases_left,
        Fin.addCases_right,CompactComplexNativeRoleBridge.single,CompactNativeRoleSourcePorts.roles]
      split_ifs with h
      · have hi : i=0 := Fin.ext h
        subst i
        rw [show (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) from rfl]
        simp only [Fin.addCases_left,Fin.addCases_right]
      · simp only [Fin.addCases_left,Fin.addCases_right]
        congr 1
        apply Fin.ext
        change i.val-1+1=i.val
        omega

private theorem outside (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw nextRaw : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload nextPayload : Tapes (1+c) 2) (aux : Tapes 2 2)
    (i : Fin (CompactComplexNonleafRoleSplit.tapes s c))
    (hi : ∀ j,CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) j≠i) :
    (caller control queue scalar raw tail storage payload aux).head i=
      (caller control queue scalar nextRaw tail storage nextPayload aux).head i ∧
    (caller control queue scalar raw tail storage payload aux).tape i=
      (caller control queue scalar nextRaw tail storage nextPayload aux).tape i := by
  constructor
  all_goals induction i using Fin.addCases (m:=CompactComplexNativeCodecFrame.permanentTapes s c) (n:=9) with
  | right i => simp only [caller,Tapes.append,Fin.addCases_right]
  | left i =>
    induction i using Fin.addCases (m:=CompactComplexControllerNativeFrame.tapes (s+43)) (n:=c) with
    | right j =>
      exfalso
      apply hi (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))
      rw [slot_payload]
      simp only [Fin.val_natAdd]
      split_ifs with h
      · omega
      · apply Fin.ext
        simp only [CompactComplexNativeRoleBridge.roleSlot,Fin.val_castAdd,Fin.val_natAdd]
        omega
    | left i =>
      induction i using Fin.addCases (m:=43) (n:=1+(66+(s+43))) with
      | left i =>
        simp only [caller,bank,CompactComplexNativeRoleBridge.bank,
          CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left]
      | right i =>
        induction i using Fin.addCases (m:=1) (n:=66+(s+43)) with
        | left i =>
          simp only [caller,bank,CompactComplexNativeRoleBridge.bank,
            CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        | right i =>
          induction i using Fin.addCases (m:=66) (n:=s+43) with
          | right i =>
            simp only [caller,bank,CompactComplexNativeRoleBridge.bank,
              CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
          | left i =>
            induction i using Fin.addCases (m:=43) (n:=23) with
            | left j =>
              exfalso
              apply hi (Fin.castAdd _ j)
              rw [slot_header]
              rfl
            | right i =>
              induction i using Fin.addCases (m:=22) (n:=1) with
              | left i =>
                simp only [caller,bank,CompactComplexNativeRoleBridge.bank,
                  CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                  Tapes.append,Fin.addCases_left,Fin.addCases_right]
              | right i =>
                fin_cases i
                exfalso
                apply hi (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))
                rw [slot_payload]
                simp only [Fin.val_zero]
                apply Fin.ext
                rfl

private theorem extra_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw nextRaw : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload nextPayload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.extra CompactComplexNonleafRoleSplit.placement
      (caller control queue scalar raw tail storage payload aux)=
    Placement.extra CompactComplexNonleafRoleSplit.placement
      (caller control queue scalar nextRaw tail storage nextPayload aux) := by
  have hn (i : Fin (CompactComplexNonleafRoleSplit.tapes s c-
      (43+CompactNativeRoleInstall.rawCount c))) :
      ∀ j,CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) j≠
        CompactComplexNonleafRoleSplit.placement (Fin.natAdd (43+CompactNativeRoleInstall.rawCount c) i) := by
    intro j he
    have hs : CompactComplexNonleafRoleSplit.placement (s:=s) (c:=c) (Fin.castAdd _ j)=
      CompactComplexNonleafRoleSplit.slot j := by
        simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    have hh := CompactComplexNonleafRoleSplit.placement.injective (hs.trans he)
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    have := j.isLt
    omega
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (outside control queue scalar raw nextRaw tail storage payload nextPayload aux _ (hn i)).1
  · exact (outside control queue scalar raw nextRaw tail storage payload nextPayload aux _ (hn i)).2

theorem replace_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw nextRaw : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload nextPayload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.replace CompactComplexNonleafRoleSplit.placement
      (caller control queue scalar raw tail storage payload aux)
      (CompactNativeRoleOriginal.bank nextRaw nextPayload)=
      caller control queue scalar nextRaw tail storage nextPayload aux := by
  rw [←active_bank control queue scalar nextRaw tail storage nextPayload aux]
  unfold Placement.replace
  rw [extra_bank control queue scalar raw nextRaw tail storage payload nextPayload aux]
  exact Placement.view _ _

private theorem entry_eq (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    CompactComplexNonleafSpectatorTargetRestore.entry
      (bank control queue scalar raw tail storage payload) (aux.append (SharedBank.empty 7 2))=
      caller control queue scalar raw tail storage payload aux := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals rfl

theorem active_entry (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s))
      (CompactComplexNonleafSpectatorTargetRestore.entry
        (bank control queue scalar raw tail storage payload) (aux.append (SharedBank.empty 7 2)))=
      CompactNativeRoleOriginal.bank raw payload := by
  rw [entry_eq]
  exact active_bank control queue scalar raw tail storage payload aux

theorem replace_entry (control : Tapes 43 2) (queue : Tapes 1 2) (scalar raw nextRaw : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload nextPayload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.replace (CompactComplexNonleafRoleSplit.placement (s:=10+s))
      (CompactComplexNonleafSpectatorTargetRestore.entry
        (bank control queue scalar raw tail storage payload) (aux.append (SharedBank.empty 7 2)))
      (CompactNativeRoleOriginal.bank nextRaw nextPayload)=
      CompactComplexNonleafSpectatorTargetRestore.entry
        (bank control queue scalar nextRaw tail storage nextPayload) (aux.append (SharedBank.empty 7 2)) := by
  rw [entry_eq,entry_eq]
  exact replace_bank control queue scalar raw nextRaw tail storage payload nextPayload aux

end
end IntegerMultBounds.Machine.NativeEndpointCharacterSplitCaller
