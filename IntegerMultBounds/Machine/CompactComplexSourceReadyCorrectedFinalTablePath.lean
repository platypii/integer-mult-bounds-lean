import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! The genuine corrected final branch follows its actual table edge to guard0.
All physical correction, contraction, rejoin and orientation runs are derived
from tape premises, with the table join charged after their exact summed cost. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalTablePath
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadySinkCorrections (data)
open CompactComplexSourceReadyCorrectedFinal (family)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyCorrectedFinal.program

theorem positive (pcStack : Fin s) : 0<CompactComplexSourceReadyScalarWorkspace.tapes s roleCount :=
  Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt

def path (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)

private theorem sigma_hoare {t B : ℕ} {P Q : Σ q,Program t q 2} (he : P=Q)
    {before after : Tapes t 2}
    (h : HoareTime P.2 (fun z => z=before) (fun z => z=after) B) :
    HoareTime Q.2 (fun z => z=before) (fun z => z=after) B := by
  cases he
  exact h

private theorem terminal_path (headerStack pcStack liveStack : Fin s)
    (before after : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) 2) (B : ℕ)
    (h : HoareTime (CompactComplexSourceReadyCorrectedFinal.program pcStack).2
      (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3) before time 0 after := by
  apply CompactComplexFixedNodePaths.terminal_control_path
    (ht:=positive pcStack) (stack:=savedStackSlot pcStack)
    (childReturn:=CompactComplexSourceReadyActualTable.childReturn headerStack liveStack)
    (controls:=controls pcStack)
    (event:=CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack)
    (isStopped:=classify pcStack) 3 (Or.inr rfl) before after B
  exact sigma_hoare
    ((CompactComplexSourceReadyCorrectedActualTable.final_program_eq pcStack).symm.trans
      (CompactComplexSourceReadyCorrectedActualTable.control_final pcStack).symm) h

/-- Final orientation and the scalar suffix retain the saved-PC bank literally. -/
theorem output_saved (sh : Shape) (rows ell p rho left count slots right src dst target : ℕ)
    (f : Array sh rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roleCount) 2)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    let ret := (bank control queue scalar stage tail (committed storage target) payload).append frame
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      rho left count slots right src dst f ret leaf
    Placement.active (FiniteReturnStackAt.placement (savedStackSlot pcStack))
      ((CompactComplexSourceReadyOrientation.output call w f).append scratch)=
      FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack))
        (storage.head (Fin.natAdd 10 pcStack)) := by
  dsimp only
  have hs := CompactComplexSourceReadyNonleafFinalPorts.saved sh rows ell p
    rho left count slots right src dst target f control queue scalar stage tail storage payload frame leaf pcStack
  rw [CompactComplexSourceReadyCorrectedActualTable.savedStackSlot_eq,
    FiniteReturnStackAt.active_bank]
  simp only [Tapes.append,Fin.addCases_left]
  rw [←FiniteReturnStackAt.active_bank,
    CompactComplexSourceReadyOrientationInvariants.retained_savedSlot,
    FiniteReturnStackAt.active_bank]
  exact congrArg₂ FiniteReturnStack.bank hs.2 hs.1

theorem tag3_path (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (hr : 0<rows) (hd : roleCount∣rows) (hgroup : 0<rows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (hP : 2*sh.bits≤p)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (before : Wire → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (before a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (dependency : CompactRecursiveDependencyBudget.Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (hblank : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    let old := CompactComplexNativeCodec.raw v rows ell p
    let after := family v hslots ell p before
    let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
    let ret := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target
        (CompactComplexSourceReadyCorrectedRoleRejoin.payload after))
    let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
      (fun j => contracted (current-target) (after j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
    ∃ time≤((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p)+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
      ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch) time 0 ((CompactComplexSourceReadyOrientation.output call w joined).append scratch) := by
  dsimp only
  apply terminal_path headerStack pcStack liveStack
  exact CompactComplexSourceReadyCorrectedFinal.compose_runs v rows ell p
    hslots hr hd hgroup hG hA hGK hpay hP control queue scalar tail storage before hw
    current target hle hcurrent htarget dependency R base usedRows hb hu hroom frame leaf
    pcStack call older origin hstack scratch hlive hblank

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalTablePath
