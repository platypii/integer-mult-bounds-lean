import IntegerMultBounds.Machine.NativeEndpointCharacterSplitCaller
import IntegerMultBounds.Machine.NativeEndpointCharacterEntryStorage
import IntegerMultBounds.Machine.NativeEndpointCharacterEntryRoles
import IntegerMultBounds.Machine.ProgramPairSequence

/-! Actual corrected tag2: target generation, physical row splitting and
canonical source signs, with a literal endpoint and exact summed runtime. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntry
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexNonleafSpectatorTargetRestore (entry)
open CompactComplexSourceReadyWorkspace (ready)
open NativeEndpointCharacterEntryRoles (data)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] seq HoareTime CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyNonleafTargetSplit.fullProgram
  CompactComplexSourceReadyNonleafTargetSplit.program CompactComplexSourceReadyNonleafTargetSplit.splitProgram
  CompactNativeRoleOriginal.splitProgram NativeEndpointCharacterCanonicalSourceReady.program
  NativeEndpointCharacterCanonicalNamedRoles.program NativeEndpointCharacterCanonicalRoles.program
  NativeEndpointCharacterCanonicalOriginal.program

def program : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) q 2 :=
  ProgramPairSequence.pair (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
    (NativeEndpointCharacterCanonicalSourceReady.program
      (s:=s) (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)

def constant := CompactComplexSourceReadyNonleafTargetSplit.constant roleCount+
  NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+1

theorem split_runs (v : Stage sh) (k rows ell p n : ℕ)
    (hslots : v.slots=arity) (hf : v.f=arity^k)
    (hr : 0<rows) (hd : roleCount∣rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hGK : sh.guard+1≤sh.chunk)
    (_hpay : sh.payload=1) (hP : 2*sh.bits≤p)
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
    (path : CompactRecursiveDependencyBudget.Path sh.active v.left (k+1) levels frames returned)
    (R baseline usedRows : ℕ) (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    HoareTime (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount)).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage
          (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f roleCount))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail
          (NativeEndpointCharacterEntryStorage.storage storage (n+2*arity^(k+1)))
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
            (data rows ell hd f)))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch)
      (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  let raw := CompactComplexNativeCodec.raw v rows ell p
  let source := CompactNativeRoleReservedBridge.sourcePayload sh rows ell f roleCount
  let frame := aux.append (SharedBank.empty 7 2)
  let caller := entry (bank control queue scalar raw tail storage source) frame
  let stored := NativeEndpointCharacterEntryStorage.storage storage (n+2*arity^(k+1))
  have hK : 0<sh.chunk := by omega
  have hrawEq : raw=CompactSpectatorLeafSetup.raw sh rows ell p v.rho v.left (arity^k) arity
      v.right v.source.val v.target.val := by
    simp only [raw,CompactComplexNativeCodec.raw,CompactNativeRoleConjugatedLifecycle.rawState,hf,hslots]
  have hsplit := CompactComplexSourceReadyNonleafTargetSplit.runs_native_linear sh rows ell p
    ⟨v.rho,v.selectedFits⟩ v.left k v.right v.source.val v.target.val n caller
    (by rw [NativeEndpointCharacterEntryStorage.header_bank];exact congrArg (ActiveRepairRankHeadersCommands.bank (a:=2)) hrawEq)
    (by
      have h := NativeEndpointCharacterEntryStorage.caller_storage control queue scalar raw tail storage source frame (⟨7,by omega⟩ : Fin (10+s))
      exact ⟨h.1.trans hn.1,h.2.trans hn.2⟩)
    (by
      have h := NativeEndpointCharacterEntryStorage.caller_storage control queue scalar raw tail storage source frame (⟨8,by omega⟩ : Fin (10+s))
      exact ⟨h.1.trans ht.1,h.2.trans ht.2⟩)
    (by norm_num [roleCount]) hr hd hG hA hK hP f hw
    (by rw [NativeEndpointCharacterSplitCaller.active_entry,hrawEq]) path R baseline usedRows hb hu hroom hlive
  have hnext : Placement.replace CompactComplexNonleafRoleSplit.placement
      (CompactComplexSourceReadyNonleafTarget.targeted caller (n+2*arity^(k+1)))
      (CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p v.rho v.left (arity^k) arity v.right v.source.val v.target.val)
        (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f))=
      entry (bank control queue scalar raw tail stored
        (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data rows ell hd f))) frame := by
    rw [←hrawEq,NativeEndpointCharacterEntryStorage.targeted_bank]
    rw [NativeEndpointCharacterSplitCaller.replace_entry,NativeEndpointCharacterEntryRoles.payload]
  have hsplit' := hsplit.consequence
    (post' := fun z => z=ready (entry (bank control queue scalar raw tail stored
      (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data rows ell hd f))) frame))
    (fun _ h => h) (fun _ h => h.trans (congrArg ready hnext)) le_rfl
  have hfull := CompactComplexSourceReadyNonleafTargetSplit.widen_runs hsplit' scratch
  exact hfull

theorem compose_runs (v : Stage sh) (k rows ell p n : ℕ)
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
    (path : CompactRecursiveDependencyBudget.Path sh.active v.left (k+1) levels frames returned)
    (R baseline usedRows : ℕ) (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    HoareTime (ProgramPairSequence.pair
      (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
      (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage
          (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f roleCount))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail
          (NativeEndpointCharacterEntryStorage.storage storage (n+2*arity^(k+1)))
          (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
            (NativeEndpointCharacterNamedBank.data false v hslots ell p (data rows ell hd f))))
        (aux.append (SharedBank.empty 7 2))
        (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch)
      (CompactComplexSourceReadyNonleafTargetSplit.constant roleCount*CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  let frame := aux.append (SharedBank.empty 7 2)
  let stored := NativeEndpointCharacterEntryStorage.storage storage (n+2*arity^(k+1))
  have hfull := split_runs v k rows ell p n hslots hf hr hd hG hA hGK hpay hP control queue scalar tail
    storage aux hn ht f hw path R baseline usedRows hb hu hroom hlive scratch
  have hsign := NativeEndpointCharacterCanonicalSourceReady.runs false v rows ell p hslots
    hG hA hGK hpay (NativeEndpointCharacterEntryRoles.positive rows hr hd) control queue scalar tail stored
    (fun _ => blank) 0 (data rows ell hd f) (NativeEndpointCharacterEntryRoles.width rows ell p hd f hw)
    frame (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) scratch (by intro i;exact ⟨rfl,rfl⟩)
  exact ProgramPairSequence.runs
    (CompactComplexSourceReadyNonleafTargetSplit.fullProgram (s:=s) (c:=roleCount))
    (NativeEndpointCharacterCanonicalSourceReady.program
      (s:=s) (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false) hfull hsign

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntry
