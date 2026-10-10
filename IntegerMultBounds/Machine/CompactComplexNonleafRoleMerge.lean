import IntegerMultBounds.Machine.CompactComplexNonleafRoleSplit

/-! The physical inverse child payload boundary: merge the actual returned
child role arrays, compute the original parent row header, and clean all generated
headers. The returned array is arbitrary and need not equal the array at entry. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRoleSplit (slot placement tapes)

def restoreSchedule (c : ℕ) : List Op :=
  [.base (.constant 19 c),product ![4,19,26] (by decide),
    cmd (.erase 4),cmd (.copy 26 4 (by decide)),cmd (.erase 19),cmd (.erase 26)]

private theorem restore_valid (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows) :
    validSchedule (restoreSchedule c) (raw sh rows ell p rho left count slots right src dst) := by
  simp [restoreSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,hr]

private theorem restore_eval (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    execute (restoreSchedule c) (raw sh rows ell p rho left count slots right src dst)=
      raw sh (rows*c) ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [restoreSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,Nat.mul_comm]

def localProgram (c : ℕ) :=
  seq (CompactNativeRoleOriginal.mergeProgram c)
    (CompactNativeRoleOriginal.headerProgram c (restoreSchedule c))

def cost (c : ℕ) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  CompactNativeRoleOriginal.cost true ((rows/c)/c) c sh ell p rho left count slots right src dst+1+
    scheduleCost (restoreSchedule c) (raw sh (rows/c) ell p rho left count slots right src dst)

/-- Merge the actual returned child array, then restore rows physically. -/
theorem local_runs (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    HoareTime (localProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank
        (raw sh (rows/c) ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f))
      (fun v => v=CompactNativeRoleOriginal.bank
        (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (cost c sh rows ell p rho left count slots right src dst) := by
  have h0 := CompactNativeRoleReservedBridge.merges sh (rows/c) c ell p rho left count slots right src dst
    hc hr hd hG hA hK f hw
  have hq := schedule_runs (a:=2) (restoreSchedule c)
    (raw sh (rows/c) ell p rho left count slots right src dst)
    (restore_valid c sh (rows/c) ell p rho left count slots right src dst hr)
  rw [restore_eval,Nat.div_mul_cancel hparent] at hq
  have h1 := hoare_extend_eq hq (CompactNativeRoleInstall.blankRaw
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
  exact h0.seq h1

variable {s c : ℕ}
def program (s c : ℕ) := Placement.placed (localProgram c) (placement (s:=s) (c:=c))

private theorem slot_header (i : Fin 43) :
    slot (s:=s) (c:=c) (Fin.castAdd _ i)=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric i) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

private theorem slot_source :
    slot (s:=s) (c:=c) (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=s) (c:=c)) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot]

private theorem slot_role (j : Fin c) :
    slot (s:=s) (c:=c) (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=s) j) := by
  apply Fin.ext
  simp [slot,CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes]
  split_ifs <;> omega

private theorem slot_extra (i : Fin (CompactNativeRoleInstall.rawCount c))
    (hi : 1 + c ≤ i.val) :
    slot (s:=s) (c:=c) (Fin.natAdd 43 i)=
      Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c)
        (⟨i.val-(1+c),by have h := i.isLt; change i.val < (1+c)+7 at h; omega⟩ : Fin 7) := by
  apply Fin.ext
  simp only [slot,Fin.val_natAdd]
  split_ifs <;> omega

theorem active_input (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (st : State) (fword : ℤ → Fin 6) (rword : Fin c → ℤ → Fin 6)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank st)
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fword)
    (hr : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=rword j) :
    Placement.active placement (v.append (SharedBank.empty 7 2))=
      CompactNativeRoleOriginal.bank st
        (CyclicRowCopy.payload fword rword 0 (fun _ => 0)) := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  have hh0 : ∀ i : Fin 43,v.head (CompactComplexNonleafRoleEntry.numeric i)=
      (ActiveRepairRankHeadersCommands.bank (a:=2) st).head i := by
    intro i
    have h := congrArg (fun b : Tapes 43 2 => b.head i) hh
    simpa [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank] using h
  have hh1 : ∀ i : Fin 43,v.tape (CompactComplexNonleafRoleEntry.numeric i)=
      (ActiveRepairRankHeadersCommands.bank (a:=2) st).tape i := by
    intro i
    have h := congrArg (fun b : Tapes 43 2 => b.tape i) hh
    simpa [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank] using h
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [slot_header,CompactNativeRoleOriginal.bank,Tapes.append] using hh0 i
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      unfold CompactNativeRoleInstall.blankRaw
      change Fin (((((1+c)+2)+2)+1)+2) at i
      induction i using Fin.addCases with
      | right i =>
        rw [slot_extra _ (by simp only [Fin.val_natAdd]; omega)]
        simp [Tapes.append,SharedBank.empty,Fin.addCases]
        all_goals first | rfl | omega
      | left i =>
        induction i using Fin.addCases with
        | right i =>
          rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
          simp [Tapes.append,SharedBank.empty,Fin.addCases]
        | left i =>
          induction i using Fin.addCases with
          | right i =>
            rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
            simp [Tapes.append,SharedBank.empty,Fin.addCases]
          | left i =>
            induction i using Fin.addCases with
            | right i =>
              rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
              simp [Tapes.append,SharedBank.empty,Fin.addCases]
            | left i =>
              induction i using Fin.addCases with
              | left i =>
                fin_cases i
                have he : slot (s:=s) (c:=c) (Fin.natAdd 43
                    (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.castAdd c (0 : Fin 1)))))))=
                    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=s) (c:=c)) := by
                  apply Fin.ext
                  simp [slot,CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
                    CompactComplexControllerNativeFrame.nativeSlot]
                simpa [Tapes.append,CyclicRowCopy.payload,he] using hs.1
              | right j =>
                have he : slot (s:=s) (c:=c) (Fin.natAdd 43
                    (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 j))))))=
                    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=s) j) := by
                  apply Fin.ext
                  simp [slot,CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
                    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes]
                  split_ifs <;> omega
                simpa [Tapes.append,CyclicRowCopy.payload,he] using (hr j).1
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [slot_header,CompactNativeRoleOriginal.bank,Tapes.append] using hh1 i
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      unfold CompactNativeRoleInstall.blankRaw
      change Fin (((((1+c)+2)+2)+1)+2) at i
      induction i using Fin.addCases with
      | right i =>
        rw [slot_extra _ (by simp only [Fin.val_natAdd]; omega)]
        simp [Tapes.append,SharedBank.empty,Fin.addCases]
        all_goals first | rfl | omega
      | left i =>
        induction i using Fin.addCases with
        | right i =>
          rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
          simp [Tapes.append,SharedBank.empty,Fin.addCases]
        | left i =>
          induction i using Fin.addCases with
          | right i =>
            rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
            simp [Tapes.append,SharedBank.empty,Fin.addCases]
          | left i =>
            induction i using Fin.addCases with
            | right i =>
              rw [slot_extra _ (by simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
              simp [Tapes.append,SharedBank.empty,Fin.addCases]
            | left i =>
              induction i using Fin.addCases with
              | left i =>
                fin_cases i
                have he : slot (s:=s) (c:=c) (Fin.natAdd 43
                    (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.castAdd c (0 : Fin 1)))))))=
                    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=s) (c:=c)) := by
                  apply Fin.ext
                  simp [slot,CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
                    CompactComplexControllerNativeFrame.nativeSlot]
                simpa [Tapes.append,CyclicRowCopy.payload,he] using hs.2
              | right j =>
                have he : slot (s:=s) (c:=c) (Fin.natAdd 43
                    (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 j))))))=
                    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=s) j) := by
                  apply Fin.ext
                  simp [slot,CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
                    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes]
                  split_ifs <;> omega
                simpa [Tapes.append,CyclicRowCopy.payload,he] using (hr j).2


/-- Literal restored parent geometry containing the arbitrary returned array. -/
def output (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :=
  Placement.replace placement (v.append (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))

/-- Only actual current header/source/role words are required. The bank
invariant is derived here, rather than supplied as a child preparation oracle. -/
theorem actual_runs (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh (rows/c) ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh (rows/c) c ell hd f j))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=output sh rows ell p rho left count slots right src dst f v)
      (cost c sh rows ell p rho left count slots right src dst) := by
  have hinput := active_input v (raw sh (rows/c) ell p rho left count slots right src dst)
    (fun _ => blank)
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word
      (CompactNativeRoleReservedBridge.role sh (rows/c) c ell hd f j))) hh hs hroles
  have h := Placement.hoare_at
    (local_runs c sh rows ell p rho left count slots right src dst hc hr hd hparent hG hA hK f hw)
    placement (v.append (SharedBank.empty 7 2)) hinput
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem output_active (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Placement.active placement (output sh rows ell p rho left count slots right src dst f v)=
      CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c) :=
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

/-- The returned source is exactly the arbitrary completed child array. -/
theorem output_source (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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

/-- Every child role slot is physically vacant at the return boundary. -/
theorem output_roles_blank (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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

/-- Genuine nonleaf depth supplies both legal child role grouping and the
exact parent-row multiplication identity. No prepared child bank is assumed. -/
theorem descendant_runs (sh : Shape)
    (m d K j ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hK : 0<K) (hj : j+1<CompactGlobalRowPadding.depth m d)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (CompactGlobalRowPadding.rowsAt c m d K j/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh (CompactGlobalRowPadding.rowsAt c m d K j/c)
        ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ r : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape r)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape r)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh (CompactGlobalRowPadding.rowsAt c m d K j/c) c ell
            (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).2 f r))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=output sh (CompactGlobalRowPadding.rowsAt c m d K j)
        ell p rho left count slots right src dst f v)
      (cost c sh (CompactGlobalRowPadding.rowsAt c m d K j)
        ell p rho left count slots right src dst) :=
  actual_runs sh _ ell p rho left count slots right src dst hc
    (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).1
    (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).2
    (CompactGlobalRowPadding.split_divides c m d K j hc hK (by omega))
    hG hA hchunk f hw v hh hs hroles
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

/-- All parked ancestor and parent payload cells and their stack head survive
child role construction literally. The independent controller clock also survives. -/
theorem output_extra (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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

/-- All forty-three physical native header slots equal the original parent raw
bank, including every erased quotient/product work slot and clean private tape. -/
theorem output_headers (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
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

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge
