import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalTablePath
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath

/-! Actual corrected nonleaf finalization reaches the original saved call
continuation, paying the physical final body, table join, guard and saved pop.
Only the original saved stack is restored after the computed result is installed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalReturnPath
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

open CompactComplexSourceReadyCorrectedFinalTablePath (path)
open SharedPlacementAlphabet (setTape)
theorem return_path (headerStack liveStack : Fin s) (v : Stage sh) (rows ell p : ℕ)
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
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank))
    (hblankTail : ∀ z,origin≤z → older z=blank) :
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
          CompactNativeRoleTransferBudget.volume rows sh ell p)+1+((CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))+5),path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 3)
      ((CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch) time (CompactComplexScheduledPCDecode.savedPC call)
      (setTape ((CompactComplexSourceReadyOrientation.output call w joined).append scratch)
        (savedStackSlot pcStack) older origin) := by
  let old := CompactComplexNativeCodec.raw v rows ell p
  let after := family v hslots ell p before
  let ws := fun j => CompactComplexStoppedGridHandoff.words (after j)
  let payload := CompactComplexControllerExactReturn.returned ws current target
    (CompactComplexSourceReadyCorrectedRoleRejoin.payload after)
  let ret := bank control queue scalar old tail (committed storage target) payload
  let joined := CompactNativeRoleRecombine.recombine sh rows roleCount ell hd
    (fun j => contracted (current-target) (after j))
  let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val joined (ret.append frame) leaf
  let out := (CompactComplexSourceReadyOrientation.output call w joined).append scratch
  obtain ⟨time,ht,hpath⟩ := CompactComplexSourceReadyCorrectedFinalTablePath.tag3_path
    headerStack liveStack v rows ell p hslots hr hd hgroup hG hA hGK hpay hP
    control queue scalar tail storage before hw current target hle hcurrent htarget
    dependency R base usedRows hb hu hroom frame leaf pcStack call older origin hstack scratch hlive hblank
  have hsaved := CompactComplexSourceReadyCorrectedFinalTablePath.output_saved sh rows ell p
    v.rho v.left v.f v.slots v.right v.source.val v.target.val target joined
    control queue scalar old tail storage payload frame leaf pcStack call scratch
  dsimp only at hsaved
  rw [FiniteReturnStackAt.active_bank] at hsaved
  have hreturn := CompactComplexSourceReadyCorrectedSavedReturnPath.full_return_path
    headerStack pcStack liveStack call out older origin (hsaved.trans hstack) hblankTail
  refine ⟨time+((CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))+5),Nat.add_le_add_right ht _,?_⟩
  dsimp only [CompactComplexSourceReadyCorrectedFinalTablePath.path,
    CompactComplexSourceReadyCorrectedSavedReturnPath.path,CompactComplexFixedNodePaths.nodePath]
    at hpath hreturn ⊢
  exact FiniteFlowPath.append hpath hreturn

private theorem paid_return (A B C D W V : ℕ) (hV : 0<V) :
    ((A*V+1+(B*V+1+(B*V+1+C*V)))+1+D*V)+1+(W+5)≤
      (A+2*B+C+D+W+10)*V := by nlinarith

/-- Both actual table joins and the genuine saved-PC pop have a static linear bound. -/
theorem cost_linear (rows ell p : ℕ) (hr : 0<rows) (sh : Shape) :
    ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume rows sh ell p+1+
      (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
      CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount*
        CompactNativeRoleTransferBudget.volume rows sh ell p)+1+
      (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)≤
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
        2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+
        CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount+
        CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+10)*
          CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact paid_return
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
    (CompactComplexSourceReadyNonleafOrientedFinal.constant roleCount)
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3))
    (CompactNativeRoleTransferBudget.volume rows sh ell p) hV

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalReturnPath
