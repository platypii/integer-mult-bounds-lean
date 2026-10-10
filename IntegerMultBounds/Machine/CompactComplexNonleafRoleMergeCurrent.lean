import IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge

/-! Physically merge a completed node's actual Original role arrays without
changing its retained row descriptor. This is the source-ready node endpoint,
including the root; restoration of a parent's geometry is a separate boundary. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrent
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRoleSplit (slot placement tapes)
variable {s c : ℕ}

def program (s c : ℕ) :=
  Placement.placed (CompactNativeRoleOriginal.mergeProgram c) (placement (s:=s) (c:=c))

def cost (c : ℕ) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  CompactNativeRoleOriginal.cost true (rows/c) c sh ell p rho left count slots right src dst

private theorem slot_header (i : Fin 43) :
    slot (s:=s) (c:=c) (Fin.castAdd _ i)=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

/-- Literal current-node geometry containing the arbitrary returned array. -/
def output (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :=
  Placement.replace placement (v.append (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c))

/-- Literal current-node words provide the actual merger's input bank.
The unchanged complementary controller state is inherited from the caller. -/
theorem actual_runs (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh rows ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh rows c ell hd f j))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=output sh rows ell p rho left count slots right src dst f v)
      (cost c sh rows ell p rho left count slots right src dst) := by
  have hinput := CompactComplexNonleafRoleMerge.active_input v
    (raw sh rows ell p rho left count slots right src dst) (fun _ => blank)
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j))) hh hs hroles
  have h := Placement.hoare_at
    (CompactNativeRoleReservedBridge.merges sh rows c ell p rho left count slots right src dst
      hc hr hd hG hA hK f hw) placement (v.append (SharedBank.empty 7 2)) hinput
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem output_active (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Placement.active placement (output sh rows ell p rho left count slots right src dst f v)=
      CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c) :=
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

/-- The merged source is exactly the arbitrary completed current-node array. -/
theorem output_source (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.castAdd 7 CompactComplexNonleafRoleEntry.source)=0 ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.castAdd 7 CompactComplexNonleafRoleEntry.source)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f) := by
  have h := output_active sh rows ell p rho left count slots right src dst f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head sourceIndex) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape sourceIndex) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,sourceIndex_slot] at hh ht
  constructor
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,sourceIndex,
      CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append] using hh
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,sourceIndex,
      CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append] using ht

/-- Every current-node role slot is physically vacant after merging. -/
theorem output_roles_blank (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin c) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape j))=0 ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape j))=fun _ => blank := by
  have h := output_active sh rows ell p rho left count slots right src dst f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (roleIndex j)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (roleIndex j)) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,roleIndex_slot] at hh ht
  constructor
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,roleIndex,
      CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append] using hh
  · simpa [
      CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,roleIndex,
      CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append] using ht

/-- Complement tapes retain their literal cells and heads. -/
theorem output_frame (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠slot j) :
    (output sh rows ell p rho left count slots right src dst f v).head i=
      (v.append (SharedBank.empty 7 2)).head i ∧
    (output sh rows ell p rho left count slots right src dst f v).tape i=
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

/-- All parked ancestor payload cells and their stack head survive merging
literally. The independent controller clock also survives. -/
theorem output_extra (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 2) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      v.head
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      v.tape
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) := by
  simpa [Tapes.append] using output_frame sh rows ell p rho left count slots right src dst f v
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
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin (s+43)) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      v.head
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      v.tape
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) := by
  simpa [Tapes.append] using output_frame sh rows ell p rho left count slots right src dst f v
    (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))
    (storage_disjoint j)

/-- All forty-three physical native header slots retain the current-node raw
bank, including the unchanged rows and erased private header work. -/
theorem output_headers (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (i : Fin 43) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) (raw sh rows ell p rho left count slots right src dst)).head i ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i))=
      (ActiveRepairRankHeadersCommands.bank (a:=2) (raw sh rows ell p rho left count slots right src dst)).tape i := by
  have h := output_active sh rows ell p rho left count slots right src dst f v
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

/-- All seven native role-merger scratch tapes return blank at head zero. -/
theorem output_scratch (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 7) :
    (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) j)=0 ∧
    (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) j)=fun _ => blank := by
  have h := output_active sh rows ell p rho left count slots right src dst f v
  have hh := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.head (scratchIndex j)) h
  have ht := congrArg (fun w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => w.tape (scratchIndex j)) h
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,scratchIndex_slot] at hh ht
  constructor
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using hh
  · simpa [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,scratchIndex,
      Tapes.append,SharedBank.empty,Fin.addCases] using ht

/-- The unchanged-size permanent bank at the completed current-node endpoint. -/
def bank (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2 :=
  ⟨fun i => (output sh rows ell p rho left count slots right src dst f v).head (Fin.castAdd 7 i),
    fun i => (output sh rows ell p rho left count slots right src dst f v).tape (Fin.castAdd 7 i)⟩

/-- The endpoint reclaims the complete appended private workspace. -/
theorem output_eq_append (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    output sh rows ell p rho left count slots right src dst f v=
      (bank sh rows ell p rho left count slots right src dst f v).append (SharedBank.empty 7 2) := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change (output sh rows ell p rho left count slots right src dst f v).head (Fin.castAdd 7 i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst f v).head
          (SharedBank.empty 7 2).head (Fin.castAdd 7 i)
      rw [Fin.addCases_left]
      rfl
    | right i =>
      change (output sh rows ell p rho left count slots right src dst f v).head
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst f v).head
          (SharedBank.empty 7 2).head (Fin.natAdd _ i)
      rw [Fin.addCases_right]
      exact (output_scratch sh rows ell p rho left count slots right src dst f v i).1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      change (output sh rows ell p rho left count slots right src dst f v).tape (Fin.castAdd 7 i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst f v).tape
          (SharedBank.empty 7 2).tape (Fin.castAdd 7 i)
      rw [Fin.addCases_left]
      rfl
    | right i =>
      change (output sh rows ell p rho left count slots right src dst f v).tape
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
        Fin.addCases (bank sh rows ell p rho left count slots right src dst f v).tape
          (SharedBank.empty 7 2).tape (Fin.natAdd _ i)
      rw [Fin.addCases_right]
      exact (output_scratch sh rows ell p rho left count slots right src dst f v i).2

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrent
