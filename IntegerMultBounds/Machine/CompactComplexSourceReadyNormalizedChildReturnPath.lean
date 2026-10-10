import IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
import IntegerMultBounds.Machine.CompactComplexNormalizedSpectatorTargetRestore
/-! The existing decoded return machine is independent of the normalization
gap. This adapter proves its literal endpoint using a genuine Progress ledger
and the actual header-driven spectator machine, leaving the selected child
unchanged and preserving the original nonleaf API. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank (tapes storage current target control)
open CompactComplexNativeCodecFrame (permanentTapes)
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

open CompactComplexSourceReadyChildReturnPath
private theorem work_public_slot (i : Fin (permanentTapes (10+s) c+9)) :
    workEquiv s c (Fin.castAdd 10 i)=
      Fin.castAdd 10 ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm i) := by
  simp [workEquiv]
private theorem work_work_slot (i : Fin 10) :
    workEquiv s c (Fin.natAdd (permanentTapes (10+s) c+9) i)=Fin.natAdd (tapes s c) i := by
  simp [workEquiv]

private theorem full_reindex (v : Tapes (permanentTapes (10+s) c) 2) (fr : Tapes 9 2)
    (work : Tapes 10 2) :
    ((v.append fr).append work).reindex (workEquiv s c)=
      (CompactComplexNonleafSpectatorTargetRestore.entry v fr).append work := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (workEquiv s c).surjective i
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases with
  | left i => simp only [work_public_slot,Tapes.append,Fin.addCases_left,
      CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Equiv.symm_symm,
      Equiv.apply_symm_apply]
  | right i => simp only [work_work_slot,Tapes.append,Fin.addCases_right]

private theorem target_runs {selected : Fin c} {b : ℕ}
    {v w : Tapes (permanentTapes (10+s) c) 2} {fr : Tapes 9 2}
    (h : HoareTime (CompactComplexNonleafSpectatorTargetRestore.program (s:=s) selected)
      (fun z => z=CompactComplexNonleafSpectatorPlacement.full v fr)
      (fun z => z=CompactComplexNonleafSpectatorPlacement.full w fr) b)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    HoareTime (targetProgram selected)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry v fr) leaf (SharedBank.empty 10 2))
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry w fr) leaf (SharedBank.empty 10 2)) b := by
  have hh := hoare_reindex_eq h (workEquiv s c)
  simp only [CompactComplexNonleafSpectatorPlacement.full,full_reindex] at hh
  exact CompactComplexSourceReadyWorkspace.spectator_runs hh leaf

open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexNativeCodec (raw)
attribute [local irreducible] CompactComplexNonleafRoleParentPayloadContinuation.program
  CompactComplexNonleafSpectatorTargetRestore.program CompactComplexSourceReadyWorkspace.publicProgram

/-- Complete physical decoded return derives its spectator input from the real
parent payload endpoint. Scalar/source/result and saved-target premises are
original caller or completed-child invariants, never intermediate readiness. -/
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
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed gap : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+gap))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+gap))) (hcurrentHead : u.head current=1)
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
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (rows/c) ell (precision-2*sh.bits) (before j))
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hcallerPayload : payloadPart
      ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/c) ell selected source sourceHead before result)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN parentTarget ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentTarget))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits parentTarget).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits parentTarget).length → targetFrame z=blank)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    let mid := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    HoareTime (program selected headerStack liveStack)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2))
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+gap) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/c) ell source sourceHead
            (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/c) ell gap selected before result)))
        (frame mid)) leaf (SharedBank.empty 10 2))
      (timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  let pay := CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c
  let returned := NativeZeroPadding.word (NativeZeroPaddingArray.word result)
  let mid := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
  have h0 := CompactComplexNonleafRoleParentPayloadContinuation.runs_linear rho visit hactive pair coordinate
    rows ell precision result u headerStack liveStack hstacks f p e he hr hd heq hG hi ht hp hb hx hhx
    liveFrame liveHead parentLive (parentLive+gap) completed progress hstack hstackHead
    hcurrent hcurrentHead htarget htargetHead hfree selected caller hresultWidth hc hA hK
    hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
  have hs : scalarPart mid=ActiveRepairRankHeadersCommands.bank scalar :=
    (output_scalar selected caller u headerStack liveStack f p liveFrame liveHead e parentLive
      (parentLive+gap) rho visit hactive pair rows ell precision pay returned).trans hscalar
  have hm := reconstruct mid scalar (raw (parent rho visit hactive pair) rows ell precision)
    (CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/c) ell selected source sourceHead before result)
    hs ((output_raw selected caller _ returned).trans hrawCaller)
    ((output_payload selected caller _ returned).trans hcallerPayload)
  have ports := output_ports selected caller u headerStack liveStack f p liveFrame liveHead e parentLive
    (parentLive+gap) rho visit hactive pair rows ell precision pay returned
  have hrRows : 0<rows := by have := Nat.div_le_self rows c; omega
  have h1 := CompactComplexNormalizedSpectatorTargetRestore.runs_linear sh rows ell precision parentLive completed gap
    (parent rho visit hactive pair) selected progress hc hrRows hr (by omega) hA hK before result hw
    (controlPart mid) (queuePart mid) scalar (tailPart mid) (storagePart mid) source sourceHead
    ports.1 ports.2.1 (frame mid) targetFrame targetHead ledgerN parentTarget ledgerLeft ledgerExponent ledger
    (ports.2.2.2.trans htargetStack) (ports.2.2.1.trans htargetStackHead) htargetFree
  have h0w := CompactComplexSourceReadyWorkspace.public_runs h0 leaf (SharedBank.empty 10 2)
  have h1w := target_runs h1 leaf
  rw [←hm] at h1w
  have h := h0w.seq h1w
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell precision :=
      Nat.mul_pos hrRows (CompactNativeRoleTransferBudget.symbols_pos sh ell precision)
    unfold timeConstant
    rw [Nat.add_mul,Nat.add_mul]
    omega)

attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexCallReturn.addressCount
  CompactComplexCallReturn.addressWidth

/-- The actual full decoded continuation reaches the genuine unique next
original event. The selected role is derived from the original call site. -/
theorem decoded_return_path (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (u : Tapes (tapes s CompactComplexRolePhaseSite.roleCount) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/CompactComplexRolePhaseSite.roleCount) (hd : CompactComplexRolePhaseSite.roleCount ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair call.slot) (rows/CompactComplexRolePhaseSite.roleCount) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
    (ht : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : u.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed gap : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+gap))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+gap))) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) CompactComplexRolePhaseSite.roleCount) 2)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<CompactComplexRolePhaseSite.roleCount) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hrawCaller : Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller=
      ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell precision))
    (hclockCaller : caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=fun _ => blank)
    (hsourceCaller : caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision false))
    (hrolesCaller : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision true))
    (hfreeCaller : CompactComplexNonleafRoleReturn.Free (CompactComplexRolePhaseSite.role call.site)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision true) caller)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (before : Fin CompactComplexRolePhaseSite.roleCount → CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (before j))
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hcallerPayload : payloadPart
      ((setTape caller (CompactComplexNonleafRoleEntry.roleTape (CompactComplexRolePhaseSite.role call.site))
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNormalizedSpectatorHandoff.returnedPayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell (CompactComplexRolePhaseSite.role call.site) source sourceHead before result)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN parentTarget ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentTarget))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits parentTarget).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits parentTarget).length → targetFrame z=blank)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hworkspace : 0<CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount)
    (pcStack : Fin (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount))
    (childReturn : Networks.ComplexRecursiveCallSchema.Call →
      Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (controls : Fin 4 → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (event : CompactComplexCompletedLiveLower.Event →
      Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (hblock : childReturn call=⟨_,program (CompactComplexRolePhaseSite.role call.site) headerStack liveStack⟩) :
    let mid :=  CompactComplexNonleafRoleSourceReturn.output (CompactComplexRolePhaseSite.role call.site) caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    ∃ steps≤timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision+1,
      CompactComplexFixedNodePaths.nodePath hworkspace pcStack childReturn controls event isStopped
        (CompactComplexScheduledPCDecode.savedPC call)
        (CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2))
        steps (CompactComplexScheduledPCLayout.callNextPC call)
        (CompactComplexSourceReadyWorkspace.bank (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+gap) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/CompactComplexRolePhaseSite.roleCount) ell source sourceHead
            (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell gap (CompactComplexRolePhaseSite.role call.site) before result)))
        (frame mid)) leaf (SharedBank.empty 10 2)) := by
  apply CompactComplexFixedNodePaths.decoded_return_path hworkspace pcStack childReturn controls event isStopped
    call _ _ (timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision)
  rw [hblock]
  exact runs_linear rho visit hactive pair call.slot rows ell precision result u headerStack liveStack
    hstacks f p e he hr hd heq hG hi ht hp hb hx hhx liveFrame liveHead parentLive completed gap progress
    hstack hstackHead hcurrent hcurrentHead htarget htargetHead hfree (CompactComplexRolePhaseSite.role call.site)
    caller hresultWidth hc hA hK hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
    scalar hscalar before hw source sourceHead hcallerPayload targetFrame targetHead ledgerN parentTarget ledgerLeft
    ledgerExponent ledger htargetStack htargetStackHead htargetFree leaf


end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath
