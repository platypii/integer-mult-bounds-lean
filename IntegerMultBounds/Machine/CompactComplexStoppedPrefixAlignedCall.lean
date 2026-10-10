import IntegerMultBounds.Machine.CompactComplexStoppedEventProgress
import IntegerMultBounds.Machine.CompactComplexStoppedAlignedCall

/-! Physical stopped-return alignment does not require a coarse numerical
input budget. The exact scalar-prefix invariant is supplied independently by
the genuine child arithmetic and spectator signed shifts. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedPrefixAlignedCall
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (Visit arity)
open CompactComplexStoppedGridHandoff (words words_width words_nonempty words_volume
  payload childPayload payload_execute)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexChildGridPromoted (aligned)
open ButterflyAxisHeadersArithmetic
open CompactComplexSpectatorVolumeHeaders
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open CompactComplexStoppedAlignedCall (rawProgram committed publicTapes childTapes targetTapes privateTapes tapes roundtripAllowance alignmentAllowance reserved_width reserved_child)
open RecursiveChildQuotientsConstant (bits)
open CompactRecursiveDependencyBudget (Path)
variable {s c : ℕ}

/-- Literal numerator shifting and physical endpoint restoration use widths
and genuine live/target words, independently of any numerical grid envelope. -/
theorem spectator_runs (sh : Shape) (rows ell q : ℕ) (hr : 0<rows)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → Array sh rows ell)
    (hwidth : ∀ j,Width sh rows ell q (before j))
    (n : ℕ) (cur tar : Fin s) (hne : cur≠tar) (len : Fin 66)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (n+arity^k)))
    (hlength : (bank control queue scalar stage tail storage
        (childPayload sh rows ell q rho visit dir selected source head before)).head
          (CompactComplexSpectatorTargetBank.numericSlot len)=1 ∧
      (bank control queue scalar stage tail storage
        (childPayload sh rows ell q rho visit dir selected source head before)).tape
          (CompactComplexSpectatorTargetBank.numericSlot len)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits
          (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))))) :
    HoareTime (CompactComplexSpectatorTargetFamily.compile
      CompactComplexSpectatorTargetBank.roleSlot
      (CompactComplexSpectatorTargetBank.oldSlot cur) (CompactComplexSpectatorTargetBank.oldSlot tar)
      (CompactComplexSpectatorTargetBank.numericSlot len)
      (CompactComplexSpectatorTargetBank.ports_injective cur tar hne len)
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)).2
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar stage tail storage
          (childPayload sh rows ell q rho visit dir selected source head before)))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar stage tail storage
          (payload sh rows ell source head (aligned sh rows ell q rho visit dir selected before))))
      ((CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
        (130*(ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2)))+
          8*(n+arity^k)+360)) := by
  let V := ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))
  let child := childPayload sh rows ell q rho visit dir selected source head before
  have hgap : arity^k≤half sh q+1 := by
    have hb := CompactSpectatorLeafSemantics.count_le_bits sh rho visit
    unfold half ButterflyGuard.halfWidth
    omega
  have hcur := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage child cur
  have htar := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage child tar
  have hrun := CompactComplexSpectatorTargetBank.spectators_runs cur tar hne len selected
    control queue scalar stage tail storage child (fun j => words (before j)) n (n+arity^k) V
    (by omega) (RecursiveChildQuotientsConstant.bits V)
    (by intro j w hw; have hh := words_width sh rows ell q (before j) (hwidth j) w hw; omega)
    (fun j => words_nonempty sh rows ell q hr (before j) (hwidth j))
    (fun j => words_volume sh rows ell q (before j) (hwidth j))
    (RecursiveChildQuotientsConstant.bits_value V) (RecursiveChildQuotientsConstant.bits_canonical V)
    ⟨hcur.1.trans hcurrent.1,hcur.2.trans hcurrent.2⟩
    ⟨htar.1.trans htarget.1,htar.2.trans htarget.2⟩ hlength
    (by
      intro j hj
      have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage child j
      have hne' : Fin.natAdd 1 j≠Fin.natAdd 1 selected := fun he => hj (Fin.natAdd_injective _ _ he)
      refine ⟨h.1.trans ?_,h.2.trans ?_⟩
      all_goals simp only [child,childPayload,CompactNativeRoleGuardedChildCaller.setRole,setTape,
        Function.update_of_ne hne',payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right])
  have he := payload_execute sh rows ell q rho visit dir selected source head before
  simp only [Nat.add_sub_cancel_left] at hrun
  have hout := congrArg (fun pay => CompactComplexSpectatorTargetFamily.ready
    (bank control queue scalar stage tail storage pay)) he
  exact hrun.consequence (fun _ h => h) (fun _ h => h.trans hout) le_rfl

/-- Original raw geometry produces and erases the true stream-volume header;
no numerical budget is needed to execute this physical handoff. -/
theorem volume_runs (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → Array sh (roleRows headerCount rows merge) ell)
    (n : ℕ) (hwidth : ∀ j,Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (before j))
    (cur tar : Fin s) (hne : cur≠tar)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (source : ℤ → Fin 6) (head : ℤ) (rawLeft rawCount slots right src dst : ℕ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (n+arity^k))) :
    let rr := roleRows headerCount rows merge
    let q := metadataP-2*sh.bits
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho.val
      rawLeft rawCount slots right src dst
    ∃ time,
      HoareTime (CompactComplexSpectatorVolumeHandoff.program headerCount merge cur tar hne selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (childPayload sh rr ell q rho visit dir selected source head before)))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (payload sh rr ell source head (aligned sh rr ell q rho visit dir selected before)))) time ∧
      time≤scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*streamVolume sh headerCount rows ell metadataP merge+8*(n+arity^k)+360)+
        scheduleCost CompactNativeRoleHeaders.cleanup prepared+2 := by
  dsimp only
  let rr := roleRows headerCount rows merge
  let q := metadataP-2*sh.bits
  let start := childPayload sh rr ell q rho visit dir selected source head before
  let after := aligned sh rr ell q rho visit dir selected before
  have hrr : 0<rr := by cases merge <;> assumption
  have hprepare := hoare_extend_eq (prepare_runs sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge hc hr hgroup hG hA hK control queue scalar tail storage start) (SharedBank.empty 10 2)
  have hlength := prepared_length sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge control queue scalar tail storage start
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata] at hlength
  have hhandoff := spectator_runs sh rr ell q hrr rho visit dir selected before hwidth n cur tar hne 27
    control queue scalar
    (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho.val rawLeft rawCount slots right src dst)
    tail storage source head hcurrent htarget hlength
  have hcleanup := hoare_extend_eq (cleanup_runs sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge control queue scalar tail storage (payload sh rr ell source head after)) (SharedBank.empty 10 2)
  have hrun := (hprepare.seq hhandoff).seq hcleanup
  refine ⟨_,hrun,?_⟩
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata]
  simp only [rr,q]
  omega

private theorem output_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (targetN : ℕ) :
    CompactComplexControllerAlignedCommit.output (bank control queue scalar stage tail storage payload) targetN=
      bank control queue scalar stage tail (committed storage targetN) payload := by
  unfold CompactComplexControllerAlignedCommit.output CompactComplexControllerAlignedCommit.current
    CompactComplexControllerAlignedCommit.target CompactComplexSpectatorTargetBank.oldSlot
    bank CompactComplexNativeRoleBridge.bank CompactComplexControllerNativeFrame.storageSlot
    CompactComplexControllerNativeFrame.bank committed
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

theorem raw_runs (sh : Shape) (headerCount rows ell metadataP : ℕ)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/headerCount) ell)
    (n : ℕ)
    (hwidth : ∀ j,Width sh (rows/headerCount) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (rawLeft rawCount slots right src dst : ℕ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+arity^k))) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount true sh rows ell metadataP rho.val
      rawLeft rawCount slots right src dst
    let after := CompactComplexChildGridPromoted.aligned sh (rows/headerCount) ell (metadataP-2*sh.bits)
      rho visit dir selected before
    ∃ time,
      HoareTime (rawProgram (s:=s) headerCount selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (CompactComplexStoppedGridHandoff.childPayload sh (rows/headerCount) ell (metadataP-2*sh.bits)
            rho visit dir selected source head before)))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready
          (bank control queue scalar old tail (committed storage (n+arity^k))
            (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after))) time ∧
      time≤ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount true) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh headerCount rows ell metadataP true+8*(n+arity^k)+360)+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+3+
        (2*(bits n).length+4*(bits (n+arity^k)).length+15) := by
  dsimp only
  obtain ⟨time,hhand,hbound⟩ := volume_runs
    sh headerCount rows ell metadataP true hc hr hgroup hG hA hK hmetadata rho visit dir selected before
    n hwidth (⟨7,by omega⟩ : Fin (10+s)) ⟨8,by omega⟩
    (by intro h;have hv := congrArg Fin.val h;norm_num at hv) control queue scalar tail storage source head
    rawLeft rawCount slots right src dst hcurrent htarget
  let after := CompactComplexChildGridPromoted.aligned sh (rows/headerCount) ell (metadataP-2*sh.bits)
    rho visit dir selected before
  let endpoint := bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst)
    tail storage (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after)
  have hc := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst) tail storage
    (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after) ⟨7,by omega⟩
  have ht := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst) tail storage
    (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after) ⟨8,by omega⟩
  have hcommit := hoare_extend_eq (CompactComplexControllerAlignedCommit.runs endpoint n (n+arity^k)
    (hc.2.trans hcurrent.2) (hc.1.trans hcurrent.1) (ht.2.trans htarget.2) (ht.1.trans htarget.1))
    (SharedBank.empty 10 2)
  rw [output_bank] at hcommit
  have hrun := hhand.seq hcommit
  refine ⟨time+1+(2*(bits n).length+4*(bits (n+arity^k)).length+15),hrun,?_⟩
  omega

private def frame {t : ℕ} (v : Tapes t 2) (x y z : ℕ) :=
  ((v.append (SharedBank.empty x 2)).append (SharedBank.empty y 2)).append (SharedBank.empty z 2)
private def frameSlots (t x y z : ℕ) (i : Fin t) : Fin (((t+x)+y)+z) :=
  Fin.castAdd z (Fin.castAdd y (Fin.castAdd x i))
private theorem frameSlots_injective (t x y z : ℕ) : Function.Injective (frameSlots t x y z) :=
  (Fin.castAdd_injective _ _).comp ((Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _))
private theorem frame_payload {t : ℕ} (v : Tapes t 2) (x y z : ℕ) :
    SharedBank.payload (frame v x y z) (frameSlots t x y z)=v := by
  unfold frame frameSlots
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.payload_append_left]
  change SharedBank.payload (v.append (SharedBank.empty x 2)) (fun i => Fin.castAdd x (id i))=v
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.payload_identity]
private theorem frame_strip {t : ℕ} (v w : Tapes t 2) (x y z : ℕ) :
    SharedBank.strip (frame v x y z) (frameSlots t x y z)=
      SharedBank.strip (frame w x y z) (frameSlots t x y z) := by
  unfold frame frameSlots
  rw [SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
    SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
    SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left]
  change (((SharedBank.strip v id).append (SharedBank.empty x 2)).append (SharedBank.empty y 2)).append (SharedBank.empty z 2)=
    (((SharedBank.strip w id).append (SharedBank.empty x 2)).append (SharedBank.empty y 2)).append (SharedBank.empty z 2)
  rw [SharedBankFrames.strip_identity,SharedBankFrames.strip_identity]

private def adapt {t r : ℕ} (M : Program (t+10) r 2) (x y z : ℕ) :=
  Placement.placed M (CleanSubbank.placement (Fin.castAdd 10) (frameSlots t x y z)
    (frameSlots_injective t x y z))
private theorem adapt_runs {t r b : ℕ} (M : Program (t+10) r 2) (v w : Tapes t 2) (x y z : ℕ)
    (h : HoareTime M (fun a => a=CompactComplexSpectatorTargetFamily.ready v)
      (fun a => a=CompactComplexSpectatorTargetFamily.ready w) b) :
    HoareTime (adapt M x y z)
      (fun a => a=(frame v x y z).append (SharedBank.empty (t+10) 2))
      (fun a => a=(frame w x y z).append (SharedBank.empty (t+10) 2)) b := by
  apply CleanSubbank.realizes _ (Fin.castAdd 10) (frameSlots t x y z)
    (Fin.castAdd_injective _ _) (frameSlots_injective t x y z) _ _ _ _ _
    ?_ ?_ (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _) (frame_strip v w x y z) h
  · rw [CleanSubbank.payload_bank,frame_payload]
  · rw [CleanSubbank.payload_bank,frame_payload]


def ready (v : Tapes (publicTapes s c) 2) : Tapes (tapes s c) 2 :=
  (frame v 86 (childTapes s) (targetTapes s)).append (SharedBank.empty (privateTapes s c) 2)
private def codecExtend {r : ℕ} (M : Program (publicTapes s c+86) r 2) :=
  extend (extend (extend M (childTapes s)) (targetTapes s)) (privateTapes s c)
def alignmentProgram (m s c : ℕ) (selected : Fin c) := seq (seq
  (codecExtend (CompactComplexNativeCodecFrame.program c m (10+s)))
  (adapt (rawProgram (s:=s) c selected) 86 (childTapes s) (targetTapes s)))
  (codecExtend (CompactComplexNativeCodecFrame.cleanupProgram (10+s) c))

theorem alignmentProgram_eq (m s c : ℕ) (selected : Fin c) :
    alignmentProgram m s c selected = CompactComplexStoppedAlignedCall.alignmentProgram m s c selected := by
  rfl

theorem alignment_runs (sh : Shape) (m d D G K0 ell q rows : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K0) (hrow : CompactGlobalRowPadding.rowAxes c m d≤D) (hDp : 0<D)
    (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunkPos : 0<sh.chunk)
    (rho : Fin sh.chunk) (v : ActivePrefixStageParameters.Stage sh) (hrho : v.rho=rho.val)
    {left k : ℕ} (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (n : ℕ)
    (hmetadata : 2*sh.bits≤CompactNativeRoleReservedBridge.precision c m d D K0 q)
    (hwidth : ∀ j,Width sh (rows/c) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+arity^k))) :
    let metadataP := CompactNativeRoleReservedBridge.precision c m d D K0 q
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    let old := CompactComplexNativeCodec.raw v rows ell metadataP
    let prepared := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho.val
      v.left v.f v.slots v.right v.source.val v.target.val
    let after := CompactComplexChildGridPromoted.aligned sh (rows/c) ell (metadataP-2*sh.bits)
      rho visit dir selected before
    ∃ time,
      HoareTime (alignmentProgram m s c selected)
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail storage
          (CompactComplexStoppedGridHandoff.childPayload sh (rows/c) ell (metadataP-2*sh.bits)
            rho visit dir selected (fun _ => blank) 0 before)))
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail
          (committed storage (n+arity^k)) (CompactComplexStoppedGridHandoff.payload sh (rows/c) ell (fun _ => blank) 0 after))) time ∧
      time≤CompactComplexNativeCodec.prepareCost c m D K0 rho.val ell q d G+
        (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true) old+
          (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
            (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+8*(n+arity^k)+360)+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+3+
          (2*(bits n).length+4*(bits (n+arity^k)).length+15))+
        CompactComplexNativeCodec.cleanupCost ell metadataP+2 := by
  dsimp only
  let metadataP := CompactNativeRoleReservedBridge.precision c m d D K0 q
  let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
  let start := CompactComplexStoppedGridHandoff.childPayload sh (rows/c) ell (metadataP-2*sh.bits)
    rho visit dir selected (fun _ => blank) 0 before
  let after := CompactComplexChildGridPromoted.aligned sh (rows/c) ell (metadataP-2*sh.bits)
    rho visit dir selected before
  let output := CompactComplexStoppedGridHandoff.payload sh (rows/c) ell (fun _ => blank) 0 after
  have hprepare := CompactComplexNativeCodecFrame.prepare_runs c m D K0 rho.val ell q d G hc hm hd hK hrow hDp
    v rows control queue tail storage start
  have hprepare' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hprepare
    (SharedBank.empty (childTapes s) 2)) (SharedBank.empty (targetTapes s) 2))
    (SharedBank.empty (privateTapes s c) 2)
  obtain ⟨time,hraw,hbound⟩ := raw_runs sh c rows ell metadataP (by omega) hr hgroup
    hG hA hchunkPos hmetadata rho visit dir selected before n hwidth
    control queue scalar tail storage (fun _ => blank) 0 v.left v.f v.slots v.right v.source.val v.target.val
    hcurrent htarget
  have hrawState : CompactComplexNativeCodec.raw v rows ell metadataP=
      CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val v.left v.f v.slots v.right v.source.val v.target.val := by
    unfold CompactComplexNativeCodec.raw CompactNativeRoleConjugatedLifecycle.rawState
    rw [hrho]
  rw [←hrawState] at hraw
  have hraw' := adapt_runs _ _ _ 86 (childTapes s) (targetTapes s) hraw
  have hcleanup := CompactComplexNativeCodecFrame.cleanup_runs scalar v rows ell metadataP
    control queue tail (committed storage (n+arity^k)) output
  have hcleanup' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hcleanup
    (SharedBank.empty (childTapes s) 2)) (SharedBank.empty (targetTapes s) 2))
    (SharedBank.empty (privateTapes s c) 2)
  have hrun := (hprepare'.seq hraw').seq hcleanup'
  refine ⟨CompactComplexNativeCodec.prepareCost c m D K0 rho.val ell q d G+1+time+1+
    CompactComplexNativeCodec.cleanupCost ell metadataP,?_,?_⟩
  · simpa only [alignmentProgram,codecExtend,ready,frame,CleanSubbank.bank,scalar,start,output,after,metadataP] using hrun
  · rw [←hrawState] at hbound
    dsimp only [metadataP] at hbound ⊢
    omega


private theorem committed_targeted (storage : Tapes (10+s) 2) (n : ℕ) :
    committed (CompactComplexStoppedLedgerRoundtrip.targeted storage n) n=committed storage n := by
  unfold committed
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases h7 : i=(⟨7,by omega⟩ : Fin (10+s))
  all_goals first | subst i; simp [CompactComplexStoppedLedgerRoundtrip.targeted,setTape] |
    by_cases h8 : i=(⟨8,by omega⟩ : Fin (10+s))
  all_goals first | subst i; simp [CompactComplexStoppedLedgerRoundtrip.targeted,setTape] |
    simp [CompactComplexStoppedLedgerRoundtrip.targeted,setTape,h7,h8]

open CompactComplexRolePhaseSite (roleCount role)
open Networks.ComplexRecursiveCallSchema (Call)

def program (m s : ℕ) (headerStack pcStack : Fin s) (call : Call) := seq
  (extend (CompactComplexStoppedLedgerRoundtrip.program m s headerStack pcStack call) (privateTapes s roleCount))
  (alignmentProgram m s roleCount (role call.site))

attribute [local irreducible] roleCount role alignmentProgram CompactComplexStoppedLedgerRoundtrip.program
  CompactComplexNativeRoleBridge.single CompactNativeRoleGuardedChildCaller.setRole
  CompactNativeRoleReservedBridge.rolePayload CompactNativeRoleReservedBridge.role
  CompactNativeRoleSourcePorts.roles CompactComplexStoppedGridHandoff.childPayload
  CompactComplexStoppedGridHandoff.payload CompactComplexChildGridPromoted.aligned
  Networks.ComplexPhaseBudget.edges

theorem actual_runs (m d D G K0 ell q level : ℕ) (hm : 2≤m)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0) (hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (hstop : Networks.ComplexRecursiveCallSchema.stopped d (k+1)=true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (headerStack pcStack : Fin s) (hne : pcStack≠headerStack)
    (st : State) (h1 : st 1=some (k+2)) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (hn : storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) ∧ storage.head ⟨7,by omega⟩=1)
    (ht : storage.tape ⟨8,by omega⟩=(fun _ => blank) ∧ storage.head ⟨8,by omega⟩=0)
    (hw0 : storage.tape ⟨0,by omega⟩=(fun _ => blank) ∧ storage.head ⟨0,by omega⟩=0)
    (hbH : ∀ z,storage.head (Fin.natAdd 10 headerStack)≤z → storage.tape (Fin.natAdd 10 headerStack) z=blank)
    (hbP : ∀ j<CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity,
      storage.tape (Fin.natAdd 10 pcStack) (storage.head (Fin.natAdd 10 pcStack)+j)=blank)
    (hb9 : ∀ z,storage.head ⟨9,by omega⟩≤z →
      z<storage.head ⟨9,by omega⟩+1+(bits (CompactComplexDenominatorPolicy.leafTarget n (k+1))).length →
      storage.tape ⟨9,by omega⟩ z=blank)
    (f : CompactSpectatorVisitGeometry.Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q))
 :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
    let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      let before := fun j => CompactNativeRoleReservedBridge.role sh rows roleCount ell hdiv f j
      let after := CompactComplexChildGridPromoted.aligned sh (rows/roleCount) ell (metadataP-2*sh.bits)
        rho (Visit.child path.visit call.slot) (CompactComplexStoppedCallSite.direction call) (role call.site) before
      HoareTime (program m s headerStack pcStack call)
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail storage
          (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f)))
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail (committed storage targetN)
          (CompactComplexStoppedGridHandoff.payload sh (rows/roleCount) ell (fun _ => blank) 0 after))) time ∧
      time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
        alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
  let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
  let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
  obtain ⟨hdiv,roundtripTime,hroundtrip,hroundtripBound⟩ := CompactComplexStoppedLedgerRoundtrip.actual_runs
    m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path hstop pair call
    headerStack pcStack hne st h1 queue tail storage n hn ht hw0 hbH hbP hb9 f hw
  let before := fun j => CompactNativeRoleReservedBridge.role sh rows roleCount ell hdiv f j
  let after := CompactComplexChildGridPromoted.aligned sh (rows/roleCount) ell (metadataP-2*sh.bits)
    rho (Visit.child path.visit call.slot) (CompactComplexStoppedCallSite.direction call) (role call.site) before
  have hprecision := CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD
  have hmetadata : 2*sh.bits≤metadataP := hprecision.1
  have hc : 2≤roleCount := by unfold roleCount;norm_num
  have hr : 0<rows := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by omega) hK (by omega)
  have hgroup : 0<rows/roleCount := CompactComplexStoppedGridHandoff.reserved_rows_pos rows (by omega) hr hdiv
  have hwidth := reserved_width sh rows ell metadataP hdiv hmetadata f hw
  have hrow : CompactGlobalRowPadding.rowAxes roleCount m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD;omega
  have hcur := CompactComplexStoppedLedgerRoundtrip.live_frame storage targetN
  have htar := CompactComplexStoppedLedgerRoundtrip.targeted_ready storage targetN
  obtain ⟨alignmentTime,halign,halignBound⟩ := alignment_runs sh m d D G K0 ell q rows hc hm
    hd hK hrow hDp hr hgroup hG hd hK rho parent rfl (Visit.child path.visit call.slot)
    (CompactComplexStoppedCallSite.direction call) (role call.site) before n
    hmetadata hwidth (ActiveRepairRankHeadersCommands.bank st) queue tail
    (CompactComplexStoppedLedgerRoundtrip.targeted storage targetN)
    ⟨hcur.1.trans hn.2,hcur.2.trans hn.1⟩ htar
  rw [reserved_child sh rows ell metadataP hdiv rho (Visit.child path.visit call.slot)
    (CompactComplexStoppedCallSite.direction call) (role call.site) f] at halign
  rw [←show targetN=n+arity^(k+1) from rfl,committed_targeted storage targetN] at halign
  have hroundtrip' := hoare_extend_eq hroundtrip (SharedBank.empty (privateTapes s roleCount) 2)
  have hrun := hroundtrip'.seq halign
  refine ⟨hdiv,roundtripTime+1+alignmentTime,?_,?_⟩
  · apply hrun.consequence
    · rintro z rfl
      rfl
    · rintro z rfl
      rfl
    · exact le_rfl
  · change roundtripTime≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows at hroundtripBound
    change alignmentTime≤alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site) at halignBound
    have hsum := Nat.add_le_add_right (Nat.add_le_add hroundtripBound halignBound) 1
    exact (show roundtripTime+1+alignmentTime≤roundtripTime+alignmentTime+1 by omega).trans hsum

theorem actual_prefix_from_roles (m d D G K0 ell q level : ℕ) (hm : 2≤m)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0) (hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (hstop : Networks.ComplexRecursiveCallSchema.stopped d (k+1)=true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (headerStack pcStack : Fin s) (hne : pcStack≠headerStack)
    (st : State) (h1 : st 1=some (k+2)) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (hn : storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) ∧ storage.head ⟨7,by omega⟩=1)
    (ht : storage.tape ⟨8,by omega⟩=(fun _ => blank) ∧ storage.head ⟨8,by omega⟩=0)
    (hw0 : storage.tape ⟨0,by omega⟩=(fun _ => blank) ∧ storage.head ⟨0,by omega⟩=0)
    (hbH : ∀ z,storage.head (Fin.natAdd 10 headerStack)≤z → storage.tape (Fin.natAdd 10 headerStack) z=blank)
    (hbP : ∀ j<CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity,
      storage.tape (Fin.natAdd 10 pcStack) (storage.head (Fin.natAdd 10 pcStack)+j)=blank)
    (hb9 : ∀ z,storage.head ⟨9,by omega⟩≤z →
      z<storage.head ⟨9,by omega⟩+1+(bits (CompactComplexDenominatorPolicy.leafTarget n (k+1))).length →
      storage.tape ⟨9,by omega⟩ z=blank)
    (before : Fin roleCount → Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level/roleCount) ell)
    (hw : ∀ j i,(before j i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (before j i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q))
    (g p C axes : ℕ) (hp : p≤q)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (haxes : axes+arity^(k+1)≤(CompactReservationNativeRows.shape roleCount m d D G K0).bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤K0)
    (hgrid : ∀ j,Grid (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level/roleCount) ell
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q-
        2*(CompactReservationNativeRows.shape roleCount m d D G K0).bits) n
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))) (before j)) :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
    let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
    ∃ time : ℕ,
      let after := CompactComplexChildGridPromoted.aligned sh (rows/roleCount) ell (metadataP-2*sh.bits)
        rho (Visit.child path.visit call.slot) (CompactComplexStoppedCallSite.direction call) (role call.site) before
      HoareTime (program m s headerStack pcStack call)
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail storage
          (payload sh (rows/roleCount) ell (fun _ => blank) 0 before)))
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail (committed storage targetN)
          (CompactComplexStoppedGridHandoff.payload sh (rows/roleCount) ell (fun _ => blank) 0 after))) time ∧
      time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
        alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 ∧
      (∀ j,Grid sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN
        (CompactFramedScalarGrid.bound g
          (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes)))
        (after j)) ∧
      (∀ j,j≠role call.site → decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN (after j)=
        decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) n (before j)) := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  have hc : 0<roleCount := by unfold roleCount; norm_num
  have hdiv : roleCount∣rows := CompactGlobalRowPadding.split_divides roleCount m d K0 level hc hK hj
  let f := CompactComplexStoppedEventProgress.reserved sh rows roleCount ell hdiv before
  have hwidth := CompactComplexStoppedEventProgress.reserved_width sh rows roleCount ell
    (CompactNativeRoleHeaders.recordWidth sh metadataP) hdiv before hw
  obtain ⟨hdiv',time,hrun,hbound⟩ := actual_runs m d D G K0 ell q level hm hDd hd hG hK hDp hD hj
    rho path hstop pair call headerStack pcStack hne st h1 queue tail storage n hn ht hw0 hbH hbP hb9 f hwidth
  have hroles : (fun j => CompactNativeRoleReservedBridge.role sh rows roleCount ell hdiv' f j)=before := by
    funext j
    exact CompactComplexStoppedEventProgress.reserved_role sh rows roleCount ell hdiv before j
  have hpay : CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv' f =
      payload sh (rows/roleCount) ell (fun _ => blank) 0 before := by
    rw [CompactComplexStoppedGridHandoff.reserved_payload,hroles]
  rw [hroles,hpay] at hrun
  have hprecision := CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD
  have hmetadata : p+2*sh.bits≤metadataP := by
    have hsub : p≤metadataP-2*sh.bits := by
      dsimp only [metadataP,sh]
      rw [hprecision.2]
      omega
    have hb : 2*sh.bits≤metadataP := hprecision.1
    omega
  have ha0 : 0<sh.active := by
    change 0<(CompactReservationNativeRows.shape roleCount m d D G K0).active
    have hv := path.visit.fits
    have hpow : 0<arity^(k+2) := pow_pos (by decide) _
    omega
  have hwg : ∀ j,Width sh (rows/roleCount) ell (metadataP-2*sh.bits) (before j) := by
    have h := reserved_width sh rows ell metadataP hdiv hprecision.1 f hwidth
    intro j
    simpa only [f,CompactComplexStoppedEventProgress.reserved_role] using h j
  have hguard := CompactComplexStoppedEventProgress.prefix_guard_from_path path g p C axes
    (arity^(k+1)) metadataP ha0 hmetadata haxes hC hroom
  have hprefix := CompactComplexStoppedEventProgress.stopped_prefix_grid sh (rows/roleCount) ell
    (metadataP-2*sh.bits) rho (Visit.child path.visit call.slot)
    (CompactComplexStoppedCallSite.direction call) (role call.site) before
    g p C levels frames returned axes n hwg hgrid hguard
  exact ⟨time,hrun,hbound,hprefix.1,hprefix.2⟩

theorem program_eq (m s : ℕ) (headerStack pcStack : Fin s) (call : Call) :
    program m s headerStack pcStack call =
      CompactComplexStoppedAlignedCall.program m s headerStack pcStack call := by
  unfold program CompactComplexStoppedAlignedCall.program
  rw [alignmentProgram_eq]

theorem ready_eq (v : Tapes (publicTapes s c) 2) :
    ready v = CompactComplexStoppedAlignedCall.ready v := by
  rfl

end
end IntegerMultBounds.Machine.CompactComplexStoppedPrefixAlignedCall
