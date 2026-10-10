import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparationBudget
import IntegerMultBounds.Machine.CompactComplexRolePhaseSite
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! Actual selected child entry on the depth-independent workspace and its
reachable event-to-shared-entry path. No local execution or cost is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyChildEntryPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRolePreparation
open CompactComplexNonleafRoleChildBankBudget (Ledger)
open CompactComplexSourceReadyWorkspace (bank)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexCompletedLiveLower (Event schedule)
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
variable {sh : Shape} {left k s : ℕ}
local notation "c" => CompactComplexRolePhaseSite.roleCount

def selected (call : Call) := CompactComplexRolePhaseSite.role call.site

def program (headerStack pcStack liveStack : Fin s) (call : Call) :=
  CompactComplexSourceReadyWorkspace.publicProgram
    (childEntryProgram (selected call) headerStack pcStack liveStack call.site call.slot)

def publicOutput (call : Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) :=
  CompactComplexNonleafRoleChildBank.output
    (sourceReady (selected call) rho visit hactive pair rows ell p f v)
    parentTarget n (k+2) headerStack pcStack liveStack call.site
    rho visit hactive pair call.slot (rows/c) ell p
    (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c)

def bound (rows ell p : ℕ) :=
  CompactComplexNonleafRolePreparationBudget.constant c
    Networks.ComplexRecursiveCallSchema.sites.length*volume rows sh ell p

/-- The original saved code is the actual decoded call address, without any
supplied site/address mapping or altered saved bits. -/
theorem saved_code (call : Call) :
    CompactComplexCallReturn.codeFor call.site call.slot=
      FiniteReturnStack.address
        (CompactComplexCallReturn.roomFor Networks.ComplexRecursiveCallSchema.sites.length (25^3))
        (CompactComplexScheduledPCDecode.callAddress call) :=
  CompactComplexScheduledPCDecode.saved_code call

/-- The literal child source remains intact until the shared stopping guard;
its raw geometry is synthesized and its role bank is vacant. -/
theorem public_output_active (call : Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) :
    Placement.active CompactComplexNonleafRoleSplit.placement
      (publicOutput call rho visit hactive pair rows ell p f v parentTarget n
        headerStack pcStack liveStack)=
      CompactNativeRoleOriginal.bank
        (CompactComplexNativeCodec.raw (child rho visit hactive pair call.slot) (rows/c) ell p)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c) :=
  CompactComplexNonleafRoleChildBank.output_active _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Actual call-site bits feed the saved-PC stack used by the fixed decoder. -/
theorem pc_saved (v : Tapes (CompactComplexSourceReadyWorkspace.publicTapes s c) 2)
    (pcStack : Fin s) (call : Call) :
    CompactComplexNonleafRoleChildBank.pcSaved v pcStack call.site call.slot=
      FiniteReturnStackAt.pushed
        (CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack))
        (FiniteReturnStack.address
          (CompactComplexCallReturn.roomFor Networks.ComplexRecursiveCallSchema.sites.length (25^3))
          (CompactComplexScheduledPCDecode.callAddress call)) v := by
  unfold CompactComplexNonleafRoleChildBank.pcSaved
  exact congrArg (fun code => FiniteReturnStackAt.pushed
    (@CompactComplexNonleafRoleChildBank.storage s CompactComplexRolePhaseSite.roleCount (Fin.natAdd 10 pcStack)) code v)
    (saved_code call)

theorem saved_pc (call : Call) :
    CompactComplexScheduledPCDecode.savedPC call=
      GuardedFiniteReturnExtraFlow.returnPC (extra:=4+schedule.length)
        (CompactComplexScheduledPCDecode.callAddress call) := rfl

theorem runs_linear (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      (v.append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1)
    (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val))
    (hclock : v.head CompactComplexNonleafRoleEntry.clock=0 ∧
      v.tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank))
    (hsource : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (v.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape (selected call))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) (work : Tapes 10 2) :
    HoareTime (program headerStack pcStack liveStack call)
      (fun w => w=bank (v.append (SharedBank.empty 7 2)) leaf work)
      (fun w => w=bank (publicOutput call rho visit hactive pair rows ell p f v
        parentTarget n headerStack pcStack liveStack) leaf work)
      (bound (sh:=sh) rows ell p) := by
  exact CompactComplexSourceReadyWorkspace.public_runs
    (CompactComplexNonleafRolePreparationBudget.child_entry_from_caller_linear (selected call) rho visit hactive pair call.slot rows ell p f v
    parentTarget n headerStack pcStack liveStack call.site ledger hx ht hh hn hp
    (by norm_num [CompactComplexRolePhaseSite.roleCount]) hr hgroup hG hA hK
    hraw hclock hsource hroles hf) leaf work

theorem child_entry_path (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      (v.append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1)
    (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val))
    (hclock : v.head CompactComplexNonleafRoleEntry.clock=0 ∧
      v.tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank))
    (hsource : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (v.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape (selected call))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) (work : Tapes 10 2)
    (hworkspace : 0<CompactComplexSourceReadyWorkspace.tapes s c)
    (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (childReturn : Call → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (controls : Fin 4 → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (event : Event → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (i : Fin schedule.length) (hi : schedule.get i=Event.child call)
    (hblock : event (Event.child call)=⟨_,program headerStack pcStack liveStack call⟩) :
    ∃ steps≤bound (sh:=sh) rows ell p+1,
      CompactComplexFixedNodePaths.nodePath hworkspace stack childReturn controls event isStopped
        (CompactComplexScheduledPCLayout.eventPC i)
        (bank (v.append (SharedBank.empty 7 2)) leaf work) steps
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
        (bank (publicOutput call rho visit hactive pair rows ell p f v
          parentTarget n headerStack pcStack liveStack) leaf work) := by
  apply CompactComplexFixedNodePaths.child_prefix_path hworkspace stack childReturn controls event isStopped
    i call hi _ _ (bound (sh:=sh) rows ell p)
  rw [hblock]
  exact runs_linear call rho visit hactive pair rows ell p f v parentTarget n
    headerStack pcStack liveStack ledger hx ht hh hn hp hr hgroup hG hA hK
    hraw hclock hsource hroles hf leaf work

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyChildEntryPath
