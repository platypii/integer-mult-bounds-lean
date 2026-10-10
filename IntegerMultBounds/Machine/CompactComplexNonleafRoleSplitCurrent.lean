import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget

/-! The genuine nonleaf branch splits the current source-ready Original array.
The current raw row geometry remains unchanged; no entry quotient or ChildBank
execution is required. The same boundary applies at a root node. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleSplitCurrent
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRoleSplit (slot placement tapes)
variable {s c : ℕ}

def program (s c : ℕ) :=
  Placement.placed (CompactNativeRoleOriginal.splitProgram c) (placement (s:=s) (c:=c))

def cost (c : ℕ) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  CompactNativeRoleOriginal.cost false (rows/c) c sh ell p rho left count slots right src dst

private theorem slot_header (i : Fin 43) :
    slot (s:=s) (c:=c) (Fin.castAdd _ i)=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

/-- Literal unchanged current-node geometry containing its cyclic role arrays. -/
def output (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :=
  Placement.replace placement (v.append (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f))

/-- Literal current-node words provide the actual splitter's input bank.
The unchanged complementary controller state is inherited from the caller. -/
theorem actual_runs (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh rows ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=
        NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=fun _ => blank) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=output sh rows ell p rho left count slots right src dst hd f v)
      (cost c sh rows ell p rho left count slots right src dst) := by
  have hinput := CompactComplexNonleafRoleMerge.active_input v
    (raw sh rows ell p rho left count slots right src dst)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (fun _ _ => blank) hh hs hroles
  have h := Placement.hoare_at
    (CompactNativeRoleReservedBridge.splits sh rows c ell p rho left count slots right src dst
      hc hr hd hG hA hK f hw) placement (v.append (SharedBank.empty 7 2)) hinput
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem output_active (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Placement.active placement (output sh rows ell p rho left count slots right src dst hd f v)=
      CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f) :=
  Placement.active_replace _ _ _

private def sourceIndex : Fin (43+CompactNativeRoleInstall.rawCount c) :=
  Fin.natAdd 43 (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.castAdd c (0 : Fin 1))))))
private def roleIndex (j : Fin c) : Fin (43+CompactNativeRoleInstall.rawCount c) :=
  Fin.natAdd 43 (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 j)))))

private theorem sourceIndex_slot : slot (s:=s) (c:=c) sourceIndex=
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=s) (c:=c)) := by
  apply Fin.ext
  simp [sourceIndex,slot,CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot]

private theorem roleIndex_slot (j : Fin c) : slot (s:=s) (c:=c) (roleIndex j)=
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=s) j) := by
  apply Fin.ext
  have h0 : ¬43+(1+j.val)<43 := by omega
  have h2 : 43+(1+j.val)<44+c := by have h := j.isLt; omega
  simp [roleIndex,slot,h0,h2,CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes]
  omega

/-- The source is physically vacant after the current-node split. -/
theorem output_source (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 CompactComplexNonleafRoleEntry.source)=0 ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 CompactComplexNonleafRoleEntry.source)=
      (fun _ => blank) := by
  have h := output_active sh rows ell p rho left count slots right src dst hd f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head sourceIndex) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape sourceIndex) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,sourceIndex_slot] at hh ht
  constructor
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,sourceIndex,
      CompactNativeRoleReservedBridge.rolePayload,CompactNativeRoleReservedBridge.rolePayload,CyclicRowCopy.payload,Tapes.append] using hh
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,sourceIndex,
      CompactNativeRoleReservedBridge.rolePayload,CompactNativeRoleReservedBridge.rolePayload,CyclicRowCopy.payload,Tapes.append] using ht

/-- Every current-node role slot contains its actual cyclic row array. -/
theorem output_roles (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin c) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape j))=0 ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape j))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word
        (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)) := by
  have h := output_active sh rows ell p rho left count slots right src dst hd f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (roleIndex j)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (roleIndex j)) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,roleIndex_slot] at hh ht
  constructor
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,roleIndex,
      CompactNativeRoleReservedBridge.rolePayload,CompactNativeRoleReservedBridge.rolePayload,CyclicRowCopy.payload,Tapes.append] using hh
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,roleIndex,
      CompactNativeRoleReservedBridge.rolePayload,CompactNativeRoleReservedBridge.rolePayload,CyclicRowCopy.payload,Tapes.append] using ht

/-- Complement tapes retain their literal cells and heads. -/
theorem output_frame (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠slot j) :
    (output sh rows ell p rho left count slots right src dst hd f v).head i=
      (v.append (SharedBank.empty 7 2)).head i ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape i=
      (v.append (SharedBank.empty 7 2)).tape i := by
  obtain ⟨i,rfl⟩ := (placement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i =>
    have he : placement (s:=s) (c:=c) (Fin.castAdd _ i)=slot i := by
      simp [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (hi i he).elim
  | right i =>
    simp only [output,Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

private theorem extra_disjoint (j : Fin 2) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j)≠slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [slot] at hv
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
    CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- All parked ancestor payload cells and their stack head survive splitting
literally. The independent controller clock also survives. -/
theorem output_extra (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 2) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      v.head
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      v.tape
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) := by
  simpa [Tapes.append] using output_frame sh rows ell p rho left count slots right src dst hd f v
    (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))
    (extra_disjoint j)

private theorem storage_disjoint (j : Fin (s+43)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
      (CompactComplexControllerNativeFrame.storageSlot j)))≠slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [slot] at hv
  simp only [Fin.val_castAdd,CompactComplexControllerNativeFrame.storageSlot,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- The complete original scalar43 bank and every retained storage tape,
including live denominator7, survive unchanged. -/
theorem output_storage (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin (s+43)) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      v.head
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      v.tape
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) := by
  simpa [Tapes.append] using output_frame sh rows ell p rho left count slots right src dst hd f v
    (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))
    (storage_disjoint j)

/-- All forty-three physical native header slots retain the current-node raw
bank, including the unchanged rows and erased private header work. -/
theorem output_headers (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (i : Fin 43) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) (raw sh rows ell p rho left count slots right src dst)).head i ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) (raw sh rows ell p rho left count slots right src dst)).tape i := by
  have h := output_active sh rows ell p rho left count slots right src dst hd f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (Fin.castAdd _ i)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (Fin.castAdd _ i)) h
  constructor
  · simpa [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,slot_header,
      CompactNativeRoleOriginal.bank,Tapes.append] using hh
  · simpa [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,slot_header,
      CompactNativeRoleOriginal.bank,Tapes.append] using ht

private def scratchIndex (j : Fin 7) : Fin (43+CompactNativeRoleInstall.rawCount c) :=
  Fin.natAdd 43 ⟨1+c+j.val, by
    have hj := j.isLt
    unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount
    omega⟩

private theorem scratchIndex_slot (j : Fin 7) :
    slot (s:=s) (c:=c) (scratchIndex j)=
      Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) j := by
  apply Fin.ext
  have hj := j.isLt
  have h0 : ¬43+(1+c+j.val)<43 := by omega
  have h2 : ¬43+(1+c+j.val)<44+c := by omega
  simp [scratchIndex, slot, h0, h2]
  omega

/-- All seven native role-splitter scratch tapes return blank at head zero. -/
theorem output_scratch (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 7) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) j)=0 ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) j)=fun _ => blank := by
  have h := output_active sh rows ell p rho left count slots right src dst hd f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (scratchIndex j)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (scratchIndex j)) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,scratchIndex_slot] at hh ht
  constructor
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using hh
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using ht

/-- The unchanged-size permanent bank at the current-node split endpoint. -/
def bank (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2 :=
  ⟨fun i => (output sh rows ell p rho left count slots right src dst hd f v).head (Fin.castAdd 7 i),
    fun i => (output sh rows ell p rho left count slots right src dst hd f v).tape (Fin.castAdd 7 i)⟩

/-- The endpoint reclaims the complete appended private workspace. -/
theorem output_eq_append (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    output sh rows ell p rho left count slots right src dst hd f v=
      (bank sh rows ell p rho left count slots right src dst hd f v).append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change (output sh rows ell p rho left count slots right src dst hd f v).head (Fin.castAdd 7 i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst hd f v).head
          (SharedBank.empty 7 2).head (Fin.castAdd 7 i)
      rw [Fin.addCases_left]
      rfl
    | right i =>
      change (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst hd f v).head
          (SharedBank.empty 7 2).head (Fin.natAdd _ i)
      rw [Fin.addCases_right]
      exact (output_scratch sh rows ell p rho left count slots right src dst hd f v i).1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change (output sh rows ell p rho left count slots right src dst hd f v).tape (Fin.castAdd 7 i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst hd f v).tape
          (SharedBank.empty 7 2).tape (Fin.castAdd 7 i)
      rw [Fin.addCases_left]
      rfl
    | right i =>
      change (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst hd f v).tape
          (SharedBank.empty 7 2).tape (Fin.natAdd _ i)
      rw [Fin.addCases_right]
      exact (output_scratch sh rows ell p rho left count slots right src dst hd f v i).2

private theorem control_disjoint (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
      (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j)))≠slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [slot] at hv
  simp only [Fin.val_castAdd,CompactComplexControllerNativeFrame.controllerSlot] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- Every physical controller tape is retained, including the actual exponent
and its private arithmetic workspace. -/
theorem output_control (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 43) :
    (output sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
          (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j))))=
      v.head (Fin.castAdd 2 (Fin.castAdd c
          (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j))) ∧
    (output sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
          (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j))))=
      v.tape (Fin.castAdd 2 (Fin.castAdd c
          (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j))) := by
  simpa only [Tapes.append,Fin.addCases_left] using
    output_frame sh rows ell p rho left count slots right src dst hd f v
      (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
        (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) j)))) (control_disjoint j)

open CompactNativeRoleTransferBudget (volume)
def constant (c : ℕ) := CompactNativeRoleOriginalBudget.constant c

theorem cost_linear (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    cost c sh rows ell p rho left count slots right src dst≤constant c*volume rows sh ell p := by
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have h := CompactNativeRoleOriginalBudget.cost_linear false (rows/c) c sh ell p rho left
    count slots right src dst hc hn hA hG hK
  rw [Nat.div_mul_cancel hd] at h
  exact h

theorem runs_linear (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hd : c ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh rows ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=
        NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=fun _ => blank):
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=(bank sh rows ell p rho left count slots right src dst hd f v).append
        (SharedBank.empty 7 2))
      (constant c*volume rows sh ell p) := by
  have h := actual_runs sh rows ell p rho left count slots right src dst hc hr hG hA hK hd f hw v hh hs hroles
  rw [output_eq_append] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear sh rows ell p rho left count slots right src dst hc hr hd hA hG hK)

open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactComplexNonleafRoleMergeCurrentBudget (path_rows)

/-- A genuine nonleaf dependency Path supplies the current divisor, including
at a root with no enclosing levels. No extra row quotient is executed. -/
theorem runs_from_path (sh : Shape) {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (d K ell p rho count slots right src dst : ℕ)
    (hc : 0<c) (hK : 0<K) (hactive : sh.active≤d) (hk : 0<k)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh
      (CompactGlobalRowPadding.rowsAt c arity d K levels) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (CompactSpectatorLeafSetup.raw sh
        (CompactGlobalRowPadding.rowsAt c arity d K levels) ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=fun _ => blank) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=(bank sh (CompactGlobalRowPadding.rowsAt c arity d K levels)
        ell p rho left count slots right src dst (path_rows path c d K hc hK hactive hk).2 f v).append (SharedBank.empty 7 2))
      (constant c*volume (CompactGlobalRowPadding.rowsAt c arity d K levels) sh ell p) :=
  runs_linear sh _ ell p rho left count slots right src dst hc
    (path_rows path c d K hc hK hactive hk).1
    hG hA hchunk (path_rows path c d K hc hK hactive hk).2 f hw v hh hs hroles


end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleSplitCurrent
