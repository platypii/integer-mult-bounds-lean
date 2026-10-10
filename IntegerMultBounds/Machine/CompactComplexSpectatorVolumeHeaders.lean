import IntegerMultBounds.Machine.CompactComplexStoppedGridHandoff

/-! Spectator stream-volume descriptors are physically generated from the
genuine retained raw geometry/ell/precision words. The selected scalar and
every old recursion slot are framed; cleanup restores the exact raw state. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
open CompactSpectatorLeafSetup (raw)
variable {s c : ℕ}

def headerProgram (ops : List Op) :=
  extend (CompactComplexControllerNativeFrame.program (s:=s+43)
    (extend (compile (a:=2) ops).2 23)) c

/-- Header arithmetic runs on the actual numeric43 bank inside native66,
with original65 source, old storage and appended scalar43 all literally framed. -/
theorem header_runs (ops : List Op) (before after : State) (time : ℕ)
    (h : HoareTime (compile (a:=2) ops).2
      (fun z => z=ActiveRepairRankHeadersCommands.bank before)
      (fun z => z=ActiveRepairRankHeadersCommands.bank after) time)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    HoareTime (headerProgram (s:=s) (c:=c) ops)
      (fun z => z=bank control queue scalar before tail storage payload)
      (fun z => z=bank control queue scalar after tail storage payload) time := by
  exact hoare_extend_eq (CompactComplexControllerNativeFrame.runs
    (hoare_extend_eq h (tail.append (CompactComplexNativeRoleBridge.single payload)))
    control queue (storage.append (ActiveRepairRankHeadersCommands.bank scalar)))
    (CompactNativeRoleSourcePorts.roles payload)

def roleRows (headerCount rows : ℕ) (merge : Bool) := if merge then rows/headerCount else rows

def streamVolume (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool) :=
  roleRows headerCount rows merge*2^sh.bits*2^ell*
    (2*(CompactNativeRoleHeaders.recordWidth sh metadataP+1))

theorem volume_semantic (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hp : 2*sh.bits≤metadataP) :
    streamVolume sh headerCount rows ell metadataP merge=
      ButterflySpectatorGeometry.Size (roleRows headerCount rows merge) sh.bits (2^ell)*
        (2*(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2)) := by
  have hw : CompactNativeRoleHeaders.recordWidth sh metadataP+1=
      CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2 := by
    simp only [CompactNativeRoleHeaders.recordWidth,ButterflyGuard.width,
      CompactSpectatorInheritedGrid.half,ButterflyGuard.halfWidth]
    omega
  rw [streamVolume,hw,CompactSpectatorVisitGeometry.coefficient_count]

theorem prepared_length (sh : Shape) (headerCount rows ell metadataP rho left count slots right source target : ℕ)
    (merge : Bool) (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    let stage := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target
    (bank control queue scalar stage tail storage payload).head
      (CompactComplexSpectatorTargetBank.numericSlot (27:Fin 66))=1 ∧
    (bank control queue scalar stage tail storage payload).tape
      (CompactComplexSpectatorTargetBank.numericSlot (27:Fin 66))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits
          (streamVolume sh headerCount rows ell metadataP merge)) := by
  simp only [CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNativeCodecFrame.bank,
    CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
    CompactComplexNativeRoleBridge.native,CompactComplexControllerNativeFrame.nativeSlot,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]
  cases merge <;> constructor <;>
    simp [CompactNativeRoleHeaders.prepared,ActiveRepairRankHeadersCommands.bank,
      CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,streamVolume,roleRows,
      Tapes.append,Fin.addCases,Nat.mul_assoc]

theorem prepare_runs (sh : Shape) (headerCount rows ell metadataP rho left count slots right source target : ℕ)
    (merge : Bool) (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    HoareTime (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule headerCount merge))
      (fun z => z=bank control queue scalar (raw sh rows ell metadataP rho left count slots right source target) tail storage payload)
      (fun z => z=bank control queue scalar
        (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target)
        tail storage payload)
      (scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge)
        (raw sh rows ell metadataP rho left count slots right source target)) :=
  header_runs _ _ _ _ (CompactNativeRoleHeaders.runs headerCount merge sh rows ell metadataP rho left count slots right source target
    hc hr hgroup hG hA hK) control queue scalar tail storage payload

theorem cleanup_runs (sh : Shape) (headerCount rows ell metadataP rho left count slots right source target : ℕ)
    (merge : Bool) (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    HoareTime (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)
      (fun z => z=bank control queue scalar
        (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target)
        tail storage payload)
      (fun z => z=bank control queue scalar (raw sh rows ell metadataP rho left count slots right source target) tail storage payload)
      (scheduleCost CompactNativeRoleHeaders.cleanup
        (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target)) :=
  header_runs _ _ _ _ (CompactNativeRoleHeaders.cleanup_runs headerCount merge sh rows ell metadataP rho left count slots right source target)
    control queue scalar tail storage payload

end
end IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHeaders
