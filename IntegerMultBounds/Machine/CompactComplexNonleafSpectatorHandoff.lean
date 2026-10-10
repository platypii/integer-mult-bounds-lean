import IntegerMultBounds.Machine.CompactComplexNonleafEventProgress
import IntegerMultBounds.Machine.CompactComplexStoppedPrefixAlignedCall
import IntegerMultBounds.Machine.CompactComplexChildAlignmentBudget

/-! Actual spectator promotion after an arbitrary normalized nonleaf result.
The old parent denominator and the actual returned target are retained while
the volume header is generated, the spectators are shifted and metadata is
erased. The common denominator must be committed only after this execution. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafSpectatorHandoff
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNonleafEventProgress (aligned)
open CompactComplexStoppedGridHandoff (words words_width words_volume words_nonempty payload words_promote)
open NativeSignedGapPromoteReturn (word)
open CompactComplexNativeCodecFrame (bank)
open ActiveRepairRankHeadersCommands (State)
open CompactComplexSpectatorVolumeHeaders
open ButterflyAxisHeadersArithmetic
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def returnedPayload (sh : Shape) (rows ell : ℕ) (selected : Fin c)
    (source : ℤ → Fin 6) (head : ℤ) (before : Fin c → Array sh rows ell)
    (child : Array sh rows ell) :=
  payload sh rows ell source head (fun j => if j=selected then child else before j)

theorem payload_execute (sh : Shape) (rows ell k : ℕ) (selected : Fin c)
    (source : ℤ → Fin 6) (head : ℤ) (before : Fin c → Array sh rows ell)
    (child : Array sh rows ell) :
    CompactComplexSpectatorRoleSchedule.execute
      (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (2*arity^(k+1)))))
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)
      (returnedPayload sh rows ell selected source head before child)=
      payload sh rows ell source head (aligned sh rows ell k selected before child) := by
  have hs := CompactComplexSpectatorRoleSchedule.execute_source
    (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (2*arity^(k+1)))))
    (CompactComplexSpectatorPromoteFamily.spectatorList selected)
    (returnedPayload sh rows ell selected source head before child)
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=1) (n:=c) with
  | left i =>
    fin_cases i
    first | exact hs.1 | exact hs.2
  | right j =>
    have h := CompactComplexSpectatorRoleSchedule.execute_slot
      (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (2*arity^(k+1)))))
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)
      (returnedPayload sh rows ell selected source head before child) j
    by_cases hj : j=selected
    · subst j
      first
      | simpa only [CompactComplexSpectatorPromoteFamily.spectatorList_mem,ne_self_iff_false,ite_false,
          returnedPayload,payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right] using h.1
      | simpa only [CompactComplexSpectatorPromoteFamily.spectatorList_mem,ne_self_iff_false,ite_false,
          returnedPayload,payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right,
          aligned,ite_true] using h.2
    · first
      | simpa [CompactComplexSpectatorPromoteFamily.spectatorList_mem,hj,returnedPayload,payload,
          CyclicRowCopy.payload,Tapes.append,aligned,words_promote] using h.1
      | simpa [CompactComplexSpectatorPromoteFamily.spectatorList_mem,hj,returnedPayload,payload,
          CyclicRowCopy.payload,Tapes.append,aligned,words_promote] using h.2

/-- The real returned array is excluded from promotion. Every spectator shifts
by twice child volume, and the selected result remains literally unchanged. -/
theorem spectator_runs (sh : Shape) (rows ell q k : ℕ) (hr : 0<rows) (selected : Fin c)
    (before : Fin c → Array sh rows ell) (child : Array sh rows ell)
    (hw : ∀ j,Width sh rows ell q (before j))
    (hcapacity : 2*arity^(k+1)≤half sh q+1)
    (n : ℕ) (cur tar : Fin s) (hne : cur≠tar) (len : Fin 66)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))))
    (hlength : (bank control queue scalar stage tail storage
      (returnedPayload sh rows ell selected source head before child)).head
        (CompactComplexSpectatorTargetBank.numericSlot len)=1 ∧
      (bank control queue scalar stage tail storage
        (returnedPayload sh rows ell selected source head before child)).tape
          (CompactComplexSpectatorTargetBank.numericSlot len)=
          RadixZeroFill.encodedBinary (bits
            (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))))) :
    HoareTime (CompactComplexSpectatorTargetFamily.compile
      CompactComplexSpectatorTargetBank.roleSlot (CompactComplexSpectatorTargetBank.oldSlot cur)
      (CompactComplexSpectatorTargetBank.oldSlot tar) (CompactComplexSpectatorTargetBank.numericSlot len)
      (CompactComplexSpectatorTargetBank.ports_injective cur tar hne len)
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)).2
      (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar stage tail storage
        (returnedPayload sh rows ell selected source head before child)))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar stage tail storage
        (payload sh rows ell source head (aligned sh rows ell k selected before child))))
      ((CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
        (130*(ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2)))+
          8*(n+2*arity^(k+1))+360)) := by
  let start := returnedPayload sh rows ell selected source head before child
  let V := ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))
  have hc := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage start cur
  have ht := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage start tar
  have hrun := CompactComplexSpectatorTargetBank.spectators_runs cur tar hne len selected
    control queue scalar stage tail storage start (fun j => words (before j)) n (n+2*arity^(k+1)) V
    (by omega) (bits V)
    (by intro j w hw';have hh := words_width sh rows ell q (before j) (hw j) w hw';omega)
    (fun j => words_nonempty sh rows ell q hr (before j) (hw j))
    (fun j => words_volume sh rows ell q (before j) (hw j))
    (RecursiveChildQuotientsConstant.bits_value V) (RecursiveChildQuotientsConstant.bits_canonical V)
    ⟨hc.1.trans hcurrent.1,hc.2.trans hcurrent.2⟩
    ⟨ht.1.trans htarget.1,ht.2.trans htarget.2⟩ hlength
    (fun j hj => by
      have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage start j
      simpa only [start,returnedPayload,payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right,
        ite_eq_right hj] using h)
  simp only [Nat.add_sub_cancel_left] at hrun
  rw [payload_execute] at hrun
  exact hrun

/-- Original raw parent geometry generates and erases the exact spectator
volume. No initialized length word or physical promotion callback is supplied. -/
theorem volume_runs (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (k : ℕ) (selected : Fin c)
    (before : Fin c → Array sh (roleRows headerCount rows merge) ell)
    (child : Array sh (roleRows headerCount rows merge) ell)
    (hcapacity : 2*arity^(k+1)≤half sh (metadataP-2*sh.bits)+1)
    (n : ℕ) (hwidth : ∀ j,Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (before j))
    (cur tar : Fin s) (hne : cur≠tar)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (source : ℤ → Fin 6) (head : ℤ) (rawRho rawLeft rawCount slots right src dst : ℕ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (n+2*arity^(k+1)))) :
    let rr := roleRows headerCount rows merge
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rawRho rawLeft rawCount slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rawRho
      rawLeft rawCount slots right src dst
    ∃ time,
      HoareTime (CompactComplexSpectatorVolumeHandoff.program headerCount merge cur tar hne selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (returnedPayload sh rr ell selected source head before child)))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (payload sh rr ell source head (aligned sh rr ell k selected before child)))) time ∧
      time≤scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*streamVolume sh headerCount rows ell metadataP merge+8*(n+2*arity^(k+1))+360)+
        scheduleCost CompactNativeRoleHeaders.cleanup prepared+2 := by
  dsimp only
  let rr := roleRows headerCount rows merge
  let q := metadataP-2*sh.bits
  let start := returnedPayload sh rr ell selected source head before child
  let after := aligned sh rr ell k selected before child
  have hrr : 0<rr := by cases merge <;> assumption
  have hprepare := hoare_extend_eq (prepare_runs sh headerCount rows ell metadataP rawRho rawLeft rawCount slots right src dst
    merge hc hr hgroup hG hA hK control queue scalar tail storage start) (SharedBank.empty 10 2)
  have hlength := prepared_length sh headerCount rows ell metadataP rawRho rawLeft rawCount slots right src dst
    merge control queue scalar tail storage start
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata] at hlength
  have hhandoff := spectator_runs sh rr ell q k hrr selected before child hwidth hcapacity n cur tar hne 27
    control queue scalar
    (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rawRho rawLeft rawCount slots right src dst)
    tail storage source head hcurrent htarget hlength
  have hcleanup := hoare_extend_eq (cleanup_runs sh headerCount rows ell metadataP rawRho rawLeft rawCount slots right src dst
    merge control queue scalar tail storage (payload sh rr ell source head after)) (SharedBank.empty 10 2)
  have hrun := (hprepare.seq hhandoff).seq hcleanup
  refine ⟨_,hrun,?_⟩
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata]
  simp only [rr,q]
  omega

private theorem output_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (targetN : ℕ) :
    CompactComplexControllerAlignedCommit.output (bank control queue scalar stage tail storage payload) targetN=
      bank control queue scalar stage tail (CompactComplexStoppedAlignedCall.committed storage targetN) payload := by
  unfold CompactComplexControllerAlignedCommit.output CompactComplexControllerAlignedCommit.current
    CompactComplexControllerAlignedCommit.target CompactComplexSpectatorTargetBank.oldSlot
    bank CompactComplexNativeRoleBridge.bank CompactComplexControllerNativeFrame.storageSlot
    CompactComplexControllerNativeFrame.bank CompactComplexStoppedAlignedCall.committed
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

/-- Only after the actual spectator shifts is the retained target physically
installed into the common live word and erased. -/
theorem raw_runs (sh : Shape) (headerCount rows ell metadataP : ℕ)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (k : ℕ) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/headerCount) ell)
    (child : Array sh (rows/headerCount) ell)
    (hcapacity : 2*arity^(k+1)≤half sh (metadataP-2*sh.bits)+1)
    (n : ℕ)
    (hwidth : ∀ j,Width sh (rows/headerCount) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (rawRho rawLeft rawCount slots right src dst : ℕ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1)))) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rawRho rawLeft rawCount slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount true sh rows ell metadataP rawRho
      rawLeft rawCount slots right src dst
    let after := aligned sh (rows/headerCount) ell k selected before child
    ∃ time,
      HoareTime (CompactComplexStoppedAlignedCall.rawProgram (s:=s) headerCount selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (returnedPayload sh (rows/headerCount) ell selected source head before child)))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready
          (bank control queue scalar old tail (CompactComplexStoppedAlignedCall.committed storage (n+2*arity^(k+1)))
            (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after))) time ∧
      time≤ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount true) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh headerCount rows ell metadataP true+8*(n+2*arity^(k+1))+360)+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+3+
        (2*(bits n).length+4*(bits (n+2*arity^(k+1))).length+15) := by
  dsimp only
  obtain ⟨time,hhand,hbound⟩ := volume_runs
    sh headerCount rows ell metadataP true hc hr hgroup hG hA hK hmetadata k selected before child hcapacity
    n hwidth (⟨7,by omega⟩ : Fin (10+s)) ⟨8,by omega⟩
    (by intro h;have hv := congrArg Fin.val h;norm_num at hv) control queue scalar tail storage source head
    rawRho rawLeft rawCount slots right src dst hcurrent htarget
  let after := aligned sh (rows/headerCount) ell k selected before child
  let endpoint := bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rawRho rawLeft rawCount slots right src dst)
    tail storage (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after)
  have hc := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rawRho rawLeft rawCount slots right src dst) tail storage
    (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after) ⟨7,by omega⟩
  have ht := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rawRho rawLeft rawCount slots right src dst) tail storage
    (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after) ⟨8,by omega⟩
  have hcommit := hoare_extend_eq (CompactComplexControllerAlignedCommit.runs endpoint n (n+2*arity^(k+1))
    (hc.2.trans hcurrent.2) (hc.1.trans hcurrent.1) (ht.2.trans htarget.2) (ht.1.trans htarget.1))
    (SharedBank.empty 10 2)
  rw [output_bank] at hcommit
  have hrun := hhand.seq hcommit
  refine ⟨time+1+(2*(bits n).length+4*(bits (n+2*arity^(k+1))).length+15),hrun,?_⟩
  omega

/-- Genuine parent/child live ledgers derive physical capacity and pay the
complete generated-volume promotion and final live commit. -/
theorem runs_linear (sh : Shape) (rows ell metadataP n completed k : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+2*arity^(k+1)))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1)))) :
    HoareTime (CompactComplexStoppedAlignedCall.rawProgram (s:=s) c selected)
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (CompactComplexStoppedAlignedCall.committed storage (n+2*arity^(k+1)))
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))))
      (CompactComplexChildAlignmentBudget.promotionConstant c*
        CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  have hcap := CompactComplexDenominatorCapacity.target_capacity progress.parentPath progress.R
    progress.baseline (metadataP-2*sh.bits) progress.parentUsed n (n+2*arity^(k+1))
    progress.base progress.parentUsed_le progress.room progress.before_live progress.target_growth
  obtain ⟨time,h,hbound⟩ := raw_runs sh c rows ell metadataP hc hr hgroup hG hA hK progress.metadata
    k selected before child (by omega) n hw control queue scalar tail storage source head
    v.rho v.left v.f v.slots v.right v.source.val v.target.val hcurrent htarget
  have hb := CompactComplexChildAlignmentBudget.promotion_linear sh c rows ell metadataP n completed
    (n+2*arity^(k+1)) v selected progress hr hgroup hG hA hK (before selected) (hw selected)
  unfold CompactComplexChildAlignmentBudget.promotionCost at hb
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (hbound.trans hb)

/-- The paid physical nonleaf handoff and genuine completed-child semantics
establish the same next caller grid, retaining the exact parent scalar prefix
and advancing its true returned-volume ledger. The recursive execution equality
and concrete child address maps are still explicit obligations. -/
theorem prefix_runs (sh : Shape) (rows ell metadataP n completed k : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+2*arity^(k+1)))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))))
    (g baselineP C axes : ℕ) (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤metadataP)
    (haxes : axes+2*arity^(k+1)≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role))
    (inputIndex : Networks.ComplexFramedExecution.Wire → CompactComplexNonleafEventProgress.Address k →
      CompactComplexNonleafEventProgress.Index sh (rows/c) ell)
    (outputWire : CompactComplexNonleafEventProgress.Index sh (rows/c) ell → Networks.ComplexFramedExecution.Wire)
    (outputAddress : CompactComplexNonleafEventProgress.Index sh (rows/c) ell → CompactComplexNonleafEventProgress.Address k)
    (hcompleted : ∀ i,decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded sh (rows/c) ell (metadataP-2*sh.bits) n
          (before selected) (inputIndex wire address)) (outputWire i) (outputAddress i)) :
    HoareTime (CompactComplexStoppedAlignedCall.rawProgram (s:=s) c selected)
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (CompactComplexStoppedAlignedCall.committed storage (n+2*arity^(k+1)))
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))))
      (CompactComplexChildAlignmentBudget.promotionConstant c*
        CompactNativeRoleTransferBudget.volume rows sh ell metadataP) ∧
    (∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (aligned sh (rows/c) ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (aligned sh (rows/c) ell k selected before child role)=
      decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have hphysical := runs_linear sh rows ell metadataP n completed k v selected progress hc hr hgroup hG hA hK
    before child hw control queue scalar tail storage source head hcurrent htarget
  have hguard := CompactComplexNonleafEventProgress.promotion_from_path progress.parentPath
    g baselineP C axes k metadataP ha hp haxes hC hroom
  have hsemantic := CompactComplexNonleafEventProgress.prefix_grid sh (rows/c) ell (metadataP-2*sh.bits)
    n k g baselineP C progress.parentLevels progress.parentFrames progress.parentReturned axes selected
    before child inputIndex outputWire outputAddress hw hg hcompleted hguard.1 hguard.2
  refine ⟨hphysical,hsemantic.1,hsemantic.2,?_⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega

end
end IntegerMultBounds.Machine.CompactComplexNonleafSpectatorHandoff
