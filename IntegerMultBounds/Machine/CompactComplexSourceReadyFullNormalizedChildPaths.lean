import IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildPaths
import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath

/-! The unchanged scalar-inclusive table executes decoded normalized returns.
The stopped specialization uses the genuine single child-volume gap, retains
all scalar scratch and reaches the original unique successor event PC. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyFullNormalizedChildPaths
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
open CompactComplexSourceReadyNormalizedChildReturnPath (runs_linear)
open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexNativeCodec (raw)
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
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
    (controls : Fin 4 → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (extra : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hworkspace : 0<CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount)
    (pcStack : Fin (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount))
    (childReturn : Networks.ComplexRecursiveCallSchema.Call →
      Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (event : CompactComplexCompletedLiveLower.Event →
      Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (hblock : childReturn call=⟨_,extend (program (CompactComplexRolePhaseSite.role call.site) headerStack liveStack) CompactComplexSourceReadyScalarWorkspace.scratch⟩) :
    let mid :=  CompactComplexNonleafRoleSourceReturn.output (CompactComplexRolePhaseSite.role call.site) caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+gap) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    ∃ steps≤timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision+1,
      CompactComplexFixedNodePaths.nodePath hworkspace pcStack childReturn controls event
        isStopped
        (CompactComplexScheduledPCDecode.savedPC call)
        ((CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2)).append extra)
        steps (CompactComplexScheduledPCLayout.callNextPC call)
        ((CompactComplexSourceReadyWorkspace.bank (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+gap) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/CompactComplexRolePhaseSite.roleCount) ell source sourceHead
            (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell gap (CompactComplexRolePhaseSite.role call.site) before result)))
        (frame mid)) leaf (SharedBank.empty 10 2)).append extra) := by
  apply CompactComplexFixedNodePaths.decoded_return_path hworkspace pcStack childReturn controls event
        isStopped
    call _ _ (timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision)
  rw [hblock]
  exact hoare_extend_eq (runs_linear rho visit hactive pair call.slot rows ell precision result u headerStack liveStack
    hstacks f p e he hr hd heq hG hi ht hp hb hx hhx liveFrame liveHead parentLive completed gap progress
    hstack hstackHead hcurrent hcurrentHead htarget htargetHead hfree (CompactComplexRolePhaseSite.role call.site)
    caller hresultWidth hc hA hK hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
    scalar hscalar before hw source sourceHead hcallerPayload targetFrame targetHead ledgerN parentTarget ledgerLeft
    ledgerExponent ledger htargetStack htargetStackHead htargetFree leaf) extra


/-- Genuine stopped return specializes the unchanged decoded continuation to
one child-volume increment, without promoting the installed selected result. -/
theorem stopped_decoded_return_path (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
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
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+arity^(k+1)))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+arity^(k+1)))) (hcurrentHead : u.head current=1)
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
    (controls : Fin 4 → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (extra : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hworkspace : 0<CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount)
    (pcStack : Fin (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount))
    (childReturn : Networks.ComplexRecursiveCallSchema.Call →
      Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (event : CompactComplexCompletedLiveLower.Event →
      Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (hblock : childReturn call=⟨_,extend (program (CompactComplexRolePhaseSite.role call.site) headerStack liveStack) CompactComplexSourceReadyScalarWorkspace.scratch⟩) :
    let mid :=  CompactComplexNonleafRoleSourceReturn.output (CompactComplexRolePhaseSite.role call.site) caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+arity^(k+1)) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    ∃ steps≤timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision+1,
      CompactComplexFixedNodePaths.nodePath hworkspace pcStack childReturn controls event
        isStopped
        (CompactComplexScheduledPCDecode.savedPC call)
        ((CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2)).append extra)
        steps (CompactComplexScheduledPCLayout.callNextPC call)
        ((CompactComplexSourceReadyWorkspace.bank (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+arity^(k+1)) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/CompactComplexRolePhaseSite.roleCount) ell source sourceHead
            (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell (arity^(k+1)) (CompactComplexRolePhaseSite.role call.site) before result)))
        (frame mid)) leaf (SharedBank.empty 10 2)).append extra) := by
  apply CompactComplexFixedNodePaths.decoded_return_path hworkspace pcStack childReturn controls event
        isStopped
    call _ _ (timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision)
  rw [hblock]
  exact hoare_extend_eq (runs_linear rho visit hactive pair call.slot rows ell precision result u headerStack liveStack
    hstacks f p e he hr hd heq hG hi ht hp hb hx hhx liveFrame liveHead parentLive completed (arity^(k+1)) progress
    hstack hstackHead hcurrent hcurrentHead htarget htargetHead hfree (CompactComplexRolePhaseSite.role call.site)
    caller hresultWidth hc hA hK hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
    scalar hscalar before hw source sourceHead hcallerPayload targetFrame targetHead ledgerN parentTarget ledgerLeft
    ledgerExponent ledger htargetStack htargetStackHead htargetFree leaf) extra


end
end IntegerMultBounds.Machine.CompactComplexSourceReadyFullNormalizedChildPaths
