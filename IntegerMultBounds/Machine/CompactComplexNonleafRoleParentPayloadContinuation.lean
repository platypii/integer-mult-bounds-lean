import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentLiveContinuation
import IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturnBudget

/-! Actual parent geometry/row/live restoration preserves the genuine parked
payload stack and clock. Its literal source-ready endpoint supplies all raw,
result and vacant-role readiness for physical payload recovery. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentPayloadContinuation
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexChildHeadersData (parent child)
open CompactComplexNativeCodec (raw)
open CompactComplexNonleafRoleChildBank (tapes numeric storage control current target)
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNativeCodecFrame (permanentTapes)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

def extra (i : Fin 2) : Fin (tapes s c) :=
  Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+s) c) i)

private theorem extra_storage (i : Fin 2) (j : Fin (10+s)) : extra (s:=s) (c:=c) i≠storage j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [extra,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  omega

private theorem extra_control (i : Fin 2) : extra (s:=s) (c:=c) i≠control 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [extra,CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  omega

private theorem extra_numeric (i : Fin 2) (j : Fin 43) : extra (s:=s) (c:=c) i≠numeric j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [extra,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  omega

private theorem small_extra (i : Fin 2) (j : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    placement (s:=s) (c:=c) (Fin.castAdd _ j)≠extra i := by
  unfold placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hj
  split_ifs at hv <;> omega

private theorem replace_extra (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (i : Fin 2) :
    (Placement.replace placement v small).head (extra i)=v.head (extra i) ∧
      (Placement.replace placement v small).tape (extra i)=v.tape (extra i) := by
  obtain ⟨j,he⟩ := (placement (s:=s) (c:=c)).surjective (extra i)
  rw [←he]
  induction j using Fin.addCases with
  | left j => exact (small_extra i j he).elim
  | right j => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

/-- The actual parked payload stack and reusable clock survive every
parent descriptor and live-word restoration step literally. -/
theorem restored_extra (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) (i : Fin 2) :
    let out := CompactComplexNonleafRoleParentLiveContinuation.output v headerStack liveStack f p liveFrame
      liveHead e parentLive childLive rho visit ha pair rows ell precision payload
    out.head (extra i)=v.head (extra i) ∧ out.tape (extra i)=v.tape (extra i) := by
  dsimp only
  have hg := CompactComplexNonleafRoleParentBank.output_frame v headerStack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e (extra i)
    (extra_control i) (extra_storage i (Fin.natAdd 10 headerStack))
    (fun j => extra_numeric i (![7,8,9] j))
  have hr := replace_extra
    (CompactComplexNonleafRoleParentBank.output v headerStack f p
      (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e)
    (CompactNativeRoleOriginal.bank (raw (parent rho visit ha pair) rows ell precision) payload) i
  have hl := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame
    (CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit ha pair
      rows ell precision payload) liveStack liveFrame liveHead parentLive childLive (extra i)
    (extra_storage i ⟨7,by omega⟩) (extra_storage i ⟨8,by omega⟩) (extra_storage i (Fin.natAdd 10 liveStack))
  exact ⟨hl.1.trans (hr.1.trans hg.1),hl.2.trans (hr.2.trans hg.2)⟩

private theorem numeric_slot (j : Fin 43) :
    placement (s:=s) (c:=c) (Fin.castAdd _ (Fin.castAdd _ j))=numeric j := by
  unfold placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot]
  omega

private theorem source_slot :
    placement (s:=s) (c:=c) (Fin.castAdd _ (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c)))))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c)) := by
  unfold placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot]

private theorem role_slot (j : Fin c) :
    placement (s:=s) (c:=c) (Fin.castAdd _ (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j))))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j) := by
  unfold placement
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,CompactComplexNonleafRoleEntry.roleTape,
    CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexControllerNativeFrame.tapes]
  split_ifs <;> omega

private theorem raw_payload (payload : Tapes (1+c) 2) (j : Fin (1+c)) :
    (CompactNativeRoleInstall.blankRaw payload).head (Fin.castAdd 7 j)=payload.head j ∧
    (CompactNativeRoleInstall.blankRaw payload).tape (Fin.castAdd 7 j)=payload.tape j := by
  have hj : Fin.castAdd 7 j = Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 j))) := by
    apply Fin.ext
    rfl
  rw [hj]
  simp only [CompactNativeRoleInstall.blankRaw,Tapes.append,Fin.addCases_left,and_self]

/-- A real source-ready raw bank supplies the protected parent-return ports;
no separately prepared header/source/role bank is required. -/
theorem ready_endpoints (u : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (returned : ℤ → Fin 6)
    (hi : Placement.active placement u=CompactNativeRoleOriginal.bank st
      (CyclicRowCopy.payload returned (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0))) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base u)=
      ActiveRepairRankHeadersCommands.bank st ∧
    ((CompactComplexNonleafRoleSourceReturn.base u).head CompactComplexNonleafRoleEntry.source=0 ∧
      (CompactComplexNonleafRoleSourceReturn.base u).tape CompactComplexNonleafRoleEntry.source=returned) ∧
    (∀ j : Fin c,(CompactComplexNonleafRoleSourceReturn.base u).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      (CompactComplexNonleafRoleSourceReturn.base u).tape (CompactComplexNonleafRoleEntry.roleTape j)=(fun _ => blank)) := by
  constructor
  · apply congrArg₂ Tapes.mk <;> funext i
    all_goals
      have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.head (Fin.castAdd _ i)) hi
      have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.tape (Fin.castAdd _ i)) hi
      simp only [Placement.active,numeric_slot,CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_left] at hh ht
      simp only [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_slot,
        CompactComplexNonleafRoleSourceReturn.base]
      first | exact hh | exact ht
  · constructor
    · have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
        b.head (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))) hi
      have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
        b.tape (Fin.natAdd 43 (Fin.castAdd 7 (0 : Fin (1+c))))) hi
      simp only [Placement.active,source_slot,CompactNativeRoleOriginal.bank,
        Tapes.append,Fin.addCases_right] at hh ht
      rw [(raw_payload _ _).1] at hh
      rw [(raw_payload _ _).2] at ht
      constructor
      · simpa [CompactComplexNonleafRoleSourceReturn.base,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,Fin.addCases_right,Fin.addCases] using hh
      · simpa [CompactComplexNonleafRoleSourceReturn.base,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,Fin.addCases_right,Fin.addCases] using ht
    · intro j
      have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
        b.head (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))) hi
      have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
        b.tape (Fin.natAdd 43 (Fin.castAdd 7 (Fin.natAdd 1 j)))) hi
      simp only [Placement.active,role_slot,CompactNativeRoleOriginal.bank,
        Tapes.append,Fin.addCases_right] at hh ht
      rw [(raw_payload _ _).1] at hh
      rw [(raw_payload _ _).2] at ht
      constructor
      · simpa [CompactComplexNonleafRoleSourceReturn.base,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,Fin.addCases_right] using hh
      · simpa [CompactComplexNonleafRoleSourceReturn.base,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,Fin.addCases_right] using ht

def program (selected : Fin c) (headerStack liveStack : Fin s) := seq
  (CompactComplexNonleafRoleParentLiveContinuation.program (c:=c) headerStack liveStack)
  (CompactComplexNonleafRoleSourceReturn.program (s:=10+s) selected)

def timeConstant (c : ℕ) := CompactComplexNonleafRoleParentLiveContinuation.timeConstant c+
  CompactComplexNonleafRoleSourceReturnBudget.constant c+1

/-- Actual parent geometry/row/live restoration is followed by generated-count
payload recovery. All intermediate raw/result/vacant-role and stack/clock
readiness is derived from the physical continuation endpoint. -/
theorem runs_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (u : Tapes (tapes s c) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/c) (hd : c ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
    (ht : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : u.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive childLive completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed childLive)
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits childLive)) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (selected : Fin c) (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<c) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hrawCaller : Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller=
      ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell precision))
    (hclockCaller : caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=fun _ => blank)
    (hsourceCaller : caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false))
    (hrolesCaller : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true))
    (hfreeCaller : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true) caller)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank) :
    HoareTime (program selected headerStack liveStack) (fun z => z=u)
      (fun z => z=CompactComplexNonleafRoleSourceReturn.output selected caller
        (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
          e parentLive childLive rho visit hactive pair rows ell precision
          (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)))
      (timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  let pay := CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c
  let next := CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit hactive pair rows ell precision pay
  have h0 := CompactComplexNonleafRoleParentLiveContinuation.runs_linear rho visit hactive pair coordinate
    rows ell precision pay u headerStack liveStack hstacks f p e he hr hd heq hG hi ht hp hb hx hhx
    liveFrame liveHead parentLive childLive completed progress hstack hstackHead hcurrent hcurrentHead
    htarget htargetHead hfree
  have hactiveNext := CompactComplexNonleafRoleParentLiveContinuation.output_active u headerStack liveStack f p
    liveFrame liveHead e parentLive childLive rho visit hactive pair rows ell precision pay
  have hready := ready_endpoints next (raw (parent rho visit hactive pair) rows ell precision)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) hactiveNext
  have hs := restored_extra u headerStack liveStack f p liveFrame liveHead e parentLive childLive
    rho visit hactive pair rows ell precision pay 0
  have hclock := restored_extra u headerStack liveStack f p liveFrame liveHead e parentLive childLive
    rho visit hactive pair rows ell precision pay 1
  have hstackNext : (CompactComplexNonleafRoleSourceReturn.base next).head CompactComplexNonleafRoleEntry.stack=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
        (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
        (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
        (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
        (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      (CompactComplexNonleafRoleSourceReturn.base next).tape CompactComplexNonleafRoleEntry.stack=
      (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
        (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
        (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
        (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
        (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack :=
    ⟨hs.1.trans hstackActual.1,hs.2.trans hstackActual.2⟩
  have hclockNext : (CompactComplexNonleafRoleSourceReturn.base next).head CompactComplexNonleafRoleEntry.clock=0 ∧
      (CompactComplexNonleafRoleSourceReturn.base next).tape CompactComplexNonleafRoleEntry.clock=fun _ => blank :=
    ⟨hclock.1.trans hclockActual.1,hclock.2.trans hclockActual.2⟩
  have hrRows : 0<rows := by have := Nat.div_le_self rows c; omega
  have h1 := CompactComplexNonleafRoleSourceReturnBudget.runs_linear selected sh rows ell precision
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val caller next result hresultWidth hc hrRows hr (by omega) hA hK
    hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hready.1 hready.2.1 hready.2.2
    hstackNext hclockNext
  have h := h0.seq h1
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell precision :=
      Nat.mul_pos hrRows (CompactNativeRoleTransferBudget.symbols_pos sh ell precision)
    unfold timeConstant
    rw [Nat.add_mul,Nat.add_mul]
    omega)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentPayloadContinuation
