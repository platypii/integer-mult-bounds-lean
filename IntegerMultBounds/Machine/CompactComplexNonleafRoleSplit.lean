import IntegerMultBounds.Machine.CompactComplexNonleafRoleEntry
import IntegerMultBounds.Machine.CompactNativeRoleReservedBridge

/-! Physical row quotient and cyclic role splitting at a genuine nonleaf child.
The parent's selected stream supplies the child source; no prepared child bank
or child split correctness oracle is required. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleSplit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd)
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)

def quotientSchedule (c : ℕ) : List Op :=
  [.base (.constant 19 c), .base (.quotient ![4,19,26] (by decide)),
    cmd (.erase 4), cmd (.copy 26 4 (by decide)), cmd (.erase 19), cmd (.erase 26)]

private theorem quotient_valid (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hc : 0<c) :
    validSchedule (quotientSchedule c) (raw sh rows ell p rho left count slots right src dst) := by
  simp [quotientSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    raw,hc]

private theorem quotient_eval (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    execute (quotientSchedule c) (raw sh rows ell p rho left count slots right src dst)=
      raw sh (rows/c) ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [quotientSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw]

def localProgram (c : ℕ) :=
  seq (CompactNativeRoleOriginal.headerProgram c (quotientSchedule c))
    (CompactNativeRoleOriginal.splitProgram c)

def cost (c : ℕ) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  scheduleCost (quotientSchedule c) (raw sh rows ell p rho left count slots right src dst)+1+
    CompactNativeRoleOriginal.cost false ((rows/c)/c) c sh ell p rho left count slots right src dst

/-- The row quotient is physically computed before the genuine selected array
is cyclically split into its own child role streams. -/
theorem local_runs (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    HoareTime (localProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank
        (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (fun v => v=CompactNativeRoleOriginal.bank
        (raw sh (rows/c) ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f))
      (cost c sh rows ell p rho left count slots right src dst) := by
  have hq := schedule_runs (a:=2) (quotientSchedule c)
    (raw sh rows ell p rho left count slots right src dst)
    (quotient_valid c sh rows ell p rho left count slots right src dst hc)
  rw [quotient_eval] at hq
  have h0 := hoare_extend_eq hq (CompactNativeRoleInstall.blankRaw
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
  have h1 := CompactNativeRoleReservedBridge.splits sh (rows/c) c ell p rho left count slots right src dst
    hc hr hd hG hA hK f hw
  exact h0.seq h1

/-- A true next descendant derives both positivity and the next role divisor. -/
theorem descendant_divides (c m d K j : ℕ) (hc : 0<c) (hK : 0<K)
    (hj : j+1<CompactGlobalRowPadding.depth m d) :
    0<CompactGlobalRowPadding.rowsAt c m d K j/c ∧
      c ∣ CompactGlobalRowPadding.rowsAt c m d K j/c := by
  rw [CompactGlobalRowPadding.next_rows c m d K j]
  exact ⟨CompactGlobalRowPadding.rowsAt_positive c m d K (j+1) hc hK (by omega),
    CompactGlobalRowPadding.split_divides c m d K (j+1) hc hK hj⟩

variable {s c : ℕ}
abbrev tapes (s c : ℕ) := CompactComplexNonleafRoleEntry.tapes s c+7

private theorem raw_size (c : ℕ) : CompactNativeRoleInstall.rawCount c=(1+c)+7 := by
  rfl

/-- The exact source and permanent role slots are retained; only the seven
clean local splitter tapes are appended to the unchanged caller. -/
def slot (i : Fin (43+CompactNativeRoleInstall.rawCount c)) : Fin (tapes s c) :=
  ⟨if i.val<43 then 44+i.val else if i.val=43 then 109
      else if i.val<44+c then 153+s+(i.val-44)
      else CompactComplexNonleafRoleEntry.tapes s c+(i.val-(44+c)), by
    have hi := i.isLt
    unfold tapes CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
      CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
      CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at *
    split_ifs <;> omega⟩

private theorem slot_val (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    (slot (s:=s) (c:=c) i).val=
      if i.val<43 then 44+i.val else if i.val=43 then 109
      else if i.val<44+c then 153+s+(i.val-44)
      else CompactComplexNonleafRoleEntry.tapes s c+(i.val-(44+c)) := rfl

private theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [slot_val,slot_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

private theorem placement_size :
    (43+CompactNativeRoleInstall.rawCount c)+
      (tapes s c-(43+CompactNativeRoleInstall.rawCount c))=tapes s c := by
  unfold tapes CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
    CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount
  omega

def placement : Fin ((43+CompactNativeRoleInstall.rawCount c)+
    (tapes s c-(43+CompactNativeRoleInstall.rawCount c))) ≃ Fin (tapes s c) :=
  InjectivePlacement.placement slot slot_injective placement_size

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

private theorem active_input (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (st : State) (fword : ℤ → Fin 6)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank st)
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fword)
    (hr : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=fun _ => blank) :
    Placement.active placement (v.append (SharedBank.empty 7 2))=
      CompactNativeRoleOriginal.bank st
        (CyclicRowCopy.payload fword (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0)) := by
  rw [placement,InjectivePlacement.active_bank]
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

/-- A literal endpoint, with all inactive caller tapes inherited from entry. -/
def output (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :=
  Placement.replace placement
    ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
      (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f))

/-- The actual entry endpoint supplies the source word and blank child role
slots. The next-depth inequality supplies the genuine child row quotient. -/
theorem actual_runs (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (program s c)
      (fun z => z=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2))
      (fun z => z=output selected sh rows ell p rho left count slots right src dst hd f v)
      (cost c sh rows ell p rho left count slots right src dst) := by
  have hsource := CompactComplexNonleafRoleEntry.output_source selected sh rows ell p rho left count slots right src dst v
  have hinput := active_input
    (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v)
    (raw sh rows ell p rho left count slots right src dst)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (CompactComplexNonleafRoleEntry.output_headers selected sh rows ell p rho left count slots right src dst v)
    ⟨hsource.1,hsource.2.trans hf⟩
    (fun j => CompactComplexNonleafRoleEntry.output_roles_blank selected j sh rows ell p rho left count slots right src dst v)
  have h := Placement.hoare_at
    (local_runs c sh rows ell p rho left count slots right src dst hc hr hd hG hA hK f hw)
    placement
    ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
      (SharedBank.empty 7 2)) hinput
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

/-- Every slot outside numeric43, source65 and the permanent role tapes is
preserved, including scalar43, the inherited live denominator and parked stack. -/
theorem output_frame (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠slot j) :
    (output selected sh rows ell p rho left count slots right src dst hd f v).head i=
      ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2)).head i ∧
    (output selected sh rows ell p rho left count slots right src dst hd f v).tape i=
      ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2)).tape i := by
  obtain ⟨i,rfl⟩ := (placement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i =>
    have he := InjectivePlacement.active_slot (slot (s:=s) (c:=c)) slot_injective placement_size i
    exact (hi i he).elim
  | right i =>
    simp only [output,Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

/-- The fixed physical program obtains its row dimensions from a real parent
level whose selected child is still nonleaf, with no divisor premise. -/
theorem descendant_runs (selected : Fin c) (sh : Shape)
    (m d K j ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hK : 0<K) (hj : j+1<CompactGlobalRowPadding.depth m d)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (CompactGlobalRowPadding.rowsAt c m d K j/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (program s c)
      (fun z => z=(CompactComplexNonleafRoleEntry.output selected sh
        (CompactGlobalRowPadding.rowsAt c m d K j) ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2))
      (fun z => z=output selected sh (CompactGlobalRowPadding.rowsAt c m d K j)
        ell p rho left count slots right src dst
        (descendant_divides c m d K j hc hK hj).2 f v)
      (cost c sh (CompactGlobalRowPadding.rowsAt c m d K j)
        ell p rho left count slots right src dst) :=
  actual_runs selected sh _ ell p rho left count slots right src dst hc
    (descendant_divides c m d K j hc hK hj).1
    (descendant_divides c m d K j hc hK hj).2 hG hA hchunk f hw v hf

/-- The installed bank contains precisely the real child quotient and cyclic
reindexings of the selected current polynomial array. -/
theorem output_active (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Placement.active placement (output selected sh rows ell p rho left count slots right src dst hd f v)=
      CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f) :=
  Placement.active_replace _ _ _

private theorem extra_disjoint (j : Fin 2) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j)≠slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  rw [slot_val] at hv
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
theorem output_extra (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 2) :
    (output selected sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) ∧
    (output selected sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape
        (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j) := by
  simpa [Tapes.append] using output_frame selected sh rows ell p rho left count slots right src dst hd f v
    (Fin.castAdd 7 (Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) j))
    (extra_disjoint j)

private theorem storage_disjoint (j : Fin (s+43)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c
      (CompactComplexControllerNativeFrame.storageSlot j)))≠slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  rw [slot_val] at hv
  simp only [Fin.val_castAdd,CompactComplexControllerNativeFrame.storageSlot,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- The complete original scalar43 bank and every retained storage tape,
including live denominator7, survive unchanged. -/
theorem output_storage (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin (s+43)) :
    (output selected sh rows ell p rho left count slots right src dst hd f v).head
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) ∧
    (output selected sh rows ell p rho left count slots right src dst hd f v).tape
        (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape
        (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))) := by
  simpa [Tapes.append] using output_frame selected sh rows ell p rho left count slots right src dst hd f v
    (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.storageSlot j))))
    (storage_disjoint j)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleSplit
