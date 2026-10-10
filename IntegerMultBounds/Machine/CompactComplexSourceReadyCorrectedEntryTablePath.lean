import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! Actual corrected nonleaf setup reaches the first original schedule PC.
Checked execution supplies the source signs, installed target and exact cost;
the original fixed table supplies its paid control edge. This is a local path,
not a recursive execution theorem. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntryTablePath
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank)
open NativeEndpointCharacterEntryRoles (data)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexFixedNodeTable
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyCorrectedEntry.program
  returnDestination eventDestination

theorem positive (pcStack : Fin s) :
    0<CompactComplexSourceReadyScalarWorkspace.tapes s CompactComplexSourceReadyScalarWorkspace.roles :=
  Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt

def path (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)

/-- Literal tag2 destination, also defined for an empty event schedule. -/
def firstEventPC (N length : ℕ) : Fin (N+(4+length)+2) :=
  if h : 0<length then GuardedFiniteReturnExtraFlow.extraPC (Fin.natAdd 4 (⟨0,h⟩ : Fin length))
  else controlPCFor N length 3

theorem split_edge (pcStack : Fin s) :
    ∀ st,controlEdgesWith (N:=originalCount) (length:=schedule.length)
      (controls pcStack) (classify pcStack) 2 st=some (firstEventPC originalCount schedule.length) :=
  fun _ => rfl

private theorem sigma_hoare {t B : ℕ} {P Q : Σ q,Program t q 2} (h : P=Q)
    {v w : Tapes t 2} (hp : HoareTime P.2 (fun z => z=v) (fun z => z=w) B) :
    HoareTime Q.2 (fun z => z=v) (fun z => z=w) B := by cases h; exact hp

private theorem sigma_control_local_path {t N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2)
    (ctrl : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (ctrl pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (i : Fin 4) (dest : Fin (N+(4+length)+2))
    (P : Σ q,Program t q 2) (hP : P=ctrl i) (before after : Tapes t 2) (B : ℕ)
    (hlocal : HoareTime P.2 (fun z => z=before) (fun z => z=after) B)
    (he : ∀ st,ce i st=some dest) :
    ∃ time≤B+1,FiniteFlowPath.Path
      (GuardedFiniteReturnExtraFlow.family (k:=k) stack
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (fun pc => (tableProgramsWith returns ctrl events pc).2))
      (GuardedFiniteReturnExtraFlow.next hN
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (tableEdgesWith returns ctrl events re ce ee))
      (controlPCFor N length i) before time dest after := by
  exact CompactComplexFixedNodePaths.control_local_path hN stack returns ctrl events re ce ee
    i dest before after B (sigma_hoare hP hlocal) he

theorem control_split_pair (pcStack : Fin s) :
    controls pcStack 2=ProgramPairSequence.pair
      (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
      (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false) := by
  exact (CompactComplexSourceReadyCorrectedActualTable.control_split pcStack).trans
    (show CompactComplexSourceReadyCorrectedEntry.program (s:=s)=_ from by
      unfold CompactComplexSourceReadyCorrectedEntry.program
      rfl)

private theorem node_split_path {t : ℕ} (ht : 0<t) (stack : Fin t)
    (childReturn : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (ctrl : Fin 4 → Σ q,Program t q 2)
    (events : CompactComplexCompletedLiveLower.Event → Σ q,Program t q 2)
    (classifier : Fin (ctrl 0).1 → Bool)
    (P : Σ q,Program t q 2) (hP : P=ctrl 2)
    (before after : Tapes t 2) (B : ℕ)
    (hactual : HoareTime P.2 (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,CompactComplexFixedNodePaths.nodePath ht stack childReturn ctrl events classifier
      (controlPCFor originalCount schedule.length 2) before time
      (firstEventPC originalCount schedule.length) after := by
  exact sigma_control_local_path
    (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht childReturn) ctrl (fun i => events (schedule.get i))
    (fun address _ => returnDestination address)
    (controlEdgesWith (N:=originalCount) (length:=schedule.length) ctrl classifier)
    (fun i _ => eventDestination i) 2 (firstEventPC originalCount schedule.length)
    P hP before after B hactual (fun _ => rfl)

private theorem split_path (headerStack pcStack liveStack : Fin s)
    (before after : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) 2) (B : ℕ)
    (hactual : HoareTime (ProgramPairSequence.pair
      (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
      (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)).2
      (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,path headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length 2) before time
      (firstEventPC originalCount schedule.length) after := by
  have hctrl : ProgramPairSequence.pair
      (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
      (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)=controls pcStack 2 := (control_split_pair pcStack).symm
  exact node_split_path (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    (ProgramPairSequence.pair
      (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
      (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)) hctrl before after B hactual


/-- Both physical joins are paid by the positive original native volume. -/
theorem cost_linear (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    CompactComplexSourceReadyNonleafTargetSplit.constant roleCount*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
      NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*CompactNativeRoleTransferBudget.volume rows sh ell p+1 ≤
    (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount+
      NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+2)*
      CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  rw [Nat.add_mul,Nat.add_mul]
  omega

theorem tag2_path (headerStack pcStack liveStack : Fin s) (v : Stage sh) (k rows ell p n : ℕ)
    (hslots : v.slots=arity) (hf : v.f=arity^k)
    (hr : 0<rows) (hd : roleCount∣rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (aux : Tapes 2 2)
    (hn : storage.head ⟨7,by omega⟩=1 ∧
      storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (ht : storage.head ⟨8,by omega⟩=0 ∧ storage.tape ⟨8,by omega⟩=(fun _ => blank))
    (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    {levels frames returned : ℕ}
    (dependency : CompactRecursiveDependencyBudget.Path sh.active v.left (k+1) levels frames returned)
    (R baseline usedRows : ℕ) (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    ∃ time≤CompactComplexSourceReadyNonleafTargetSplit.constant roleCount*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
      NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*CompactNativeRoleTransferBudget.volume rows sh ell p+1,
      path headerStack pcStack liveStack (controlPCFor originalCount schedule.length 2)
      ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage
          (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f roleCount))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch)
      time (firstEventPC originalCount schedule.length)
      ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail
          (NativeEndpointCharacterEntryStorage.storage storage (n+2*arity^(k+1)))
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
            (NativeEndpointCharacterNamedBank.data false v hslots ell p (data rows ell hd f))))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch) := by
  have hactual := CompactComplexSourceReadyCorrectedEntry.compose_runs v k rows ell p n hslots hf hr hd
    hG hA hGK hpay hP control queue scalar tail storage aux hn ht f hw dependency R baseline usedRows hb hu hroom hlive scratch
  exact split_path headerStack pcStack liveStack _ _ _ hactual

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntryTablePath
