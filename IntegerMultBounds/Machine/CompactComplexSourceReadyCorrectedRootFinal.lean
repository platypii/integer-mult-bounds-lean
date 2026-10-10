import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafRootFinal

/-! Actual root sink correction, contraction and rejoin on the unchanged
corrected program. The empty saved stack selects identity post-orientation. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootFinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexSourceReadySinkCorrections (data)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] seq HoareTime roleCount
  CompactComplexSourceReadySinkCorrections.program
  CompactComplexSourceReadyNonleafOrientedFinal.program

open CompactComplexSourceReadyCorrectedFinal (program family payload_family family_width)

theorem compose_runs (v : Stage sh) (rows ell p : ℕ)
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
    (path : CompactRecursiveDependencyBudget.Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
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
    HoareTime (program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 before))
        (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      ((NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
        (CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
          CompactNativeRoleTransferBudget.volume rows sh ell p+4)) := by
  have hsink := CompactComplexSourceReadySinkCorrections.compose_runs v rows ell p
    hslots hG hA hGK hpay hgroup control queue scalar tail storage (fun _ => blank) 0 before
    hw (frame.append (SharedBank.empty 7 2)) leaf scratch hblank
  rw [payload_family v hslots ell p before] at hsink
  have hfinal := CompactComplexSourceReadyNonleafRootFinal.family_runs_native_linear sh rows ell p
    (by unfold roleCount; omega) hr hd hgroup hG hA (by omega) hP
    v.rho v.left v.f v.slots v.right v.source.val v.target.val
    control queue scalar tail storage (family v hslots ell p before)
    (family_width v hslots ell p (CompactNativeRoleHeaders.recordWidth sh p) before hw)
    current target hle hcurrent htarget path R base usedRows hb hu hroom frame leaf
    pcStack hroot scratch hlive
  dsimp only [program]
  exact ProgramPairSequence.runs
    (CompactComplexSourceReadySinkCorrections.program (s:=s))
    (CompactComplexSourceReadyNonleafOrientedFinal.program (c:=roleCount) pcStack) hsink hfinal


private theorem paid_final (A B C D V : ℕ) (hV : 0<V) :
    (A*V+1+(B*V+1+(B*V+1+C*V)))+1+(D*V+4)≤(A+2*B+C+D+8)*V := by nlinarith

/-- The full actual corrected final branch has one static linear-volume bound. -/
theorem cost_linear (rows ell p : ℕ) (hr : 0<rows) (sh : Shape) :
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume rows sh ell p+1+
      (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume rows sh ell p)))+1+
      CompactComplexSourceReadyNonleafFinalPath.constant roleCount*
        CompactNativeRoleTransferBudget.volume rows sh ell p+4≤
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
        2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+
        CompactComplexSourceReadyNonleafFinalPath.constant roleCount+8)*
          CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  simpa only [Nat.add_assoc] using paid_final
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
    (CompactComplexSourceReadyNonleafFinalPath.constant roleCount)
    (CompactNativeRoleTransferBudget.volume rows sh ell p) hV

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootFinal
