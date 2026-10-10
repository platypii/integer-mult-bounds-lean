import IntegerMultBounds.Machine.CompactComplexStoppedLedgerRoundtrip
import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHandoff
import IntegerMultBounds.Machine.CompactComplexControllerAlignedCommit

/-! A stopped child becomes a physically installed common-grid endpoint only
through original-descriptor codec setup, generated stream-volume promotion,
paid denominator commit and exact parent-codec cleanup. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedAlignedCall
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open SharedPlacementAlphabet (setTape)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

/-- The polynomial codec modifies payload capacity, not butterfly semantics. -/
theorem result_shape (sh : Shape) (rows ell metadataP q : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k) (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell metadataP)
      rows ell q rho visit f=CompactSpectatorLeafGuardOriginal.result dir sh rows ell q rho visit f := by
  cases dir <;> simp only [CompactSpectatorLeafGuardOriginal.result,NativePolynomialStageShape.bits]
  · generalize h : arity^k=t
    clear h
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [CompactSpectatorLeafLoop.run]
      split_ifs <;> rw [ih]
      rfl
  · generalize h : arity^k=t
    clear h
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [CompactSpectatorInverseLeafLoop.run]
      split_ifs <;> rw [ih]
      rfl

/-- Literal stopped-output compatibility on the original retained shape. -/
theorem reserved_child (sh : Shape) (rows ell metadataP : ℕ) (hdiv : c∣rows)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    CompactComplexStoppedGridHandoff.childPayload sh (rows/c) ell (metadataP-2*sh.bits)
      rho visit dir selected (fun _ => blank) 0
      (fun j => CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j)=
      CompactNativeRoleGuardedChildCaller.setRole (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hdiv f)
        selected (CompactNativeRoleGuardedChildCaller.resultWord dir sh rows c ell metadataP rho visit hdiv f selected) := by
  have h := CompactComplexStoppedGridHandoff.reserved_child sh rows ell metadataP hdiv rho visit dir selected f
  unfold CompactComplexStoppedGridHandoff.childPayload at h ⊢
  rw [result_shape] at h
  exact h

/-- A single retained global width supplies every real reserved role width. -/
theorem reserved_width (sh : Shape) (rows ell metadataP : ℕ) (hdiv : c∣rows)
    (hp : 2*sh.bits≤metadataP) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh metadataP) :
    ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits)
      (CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j) := by
  apply CompactComplexStoppedGridHandoff.reserved_width sh rows ell (metadataP-2*sh.bits) hdiv f
  intro i
  have hi := hw i
  rw [CompactNativeRoleChildPrecision.stored_width sh metadataP hp] at hi
  simpa only [ButterflyAxisHeadersData.width_eq] using hi

/-- The actual child Path enlarges the parent envelope. No per-role guard
bound is supplied to the handoff. -/
theorem child_budget {active left k levels frames returned : ℕ}
    (_path : Path active left (k+2) levels frames returned)
    (call : Networks.ComplexRecursiveCallSchema.Call) (p C : ℕ) (hC : 1≤C) :
    CompactRecursiveGridBudget.bound p C levels (frames+2*returned)≤
      CompactRecursiveGridBudget.bound p C (levels+1)
        ((frames+arity^(k+2))+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1))) := by
  have hc : C^levels≤C^(levels+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hf : 4^(frames+2*returned)≤4^((frames+arity^(k+2))+
      2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1))) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left (2^p) hc) hf

def committed (storage : Tapes (10+s) 2) (targetN : ℕ) :=
  setTape (setTape storage (⟨7,by omega⟩ : Fin (10+s)) (RadixZeroFill.encodedBinary (bits targetN)) 1)
    ⟨8,by omega⟩ (fun _ => blank) 0
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

def rawProgram (headerCount : ℕ) (selected : Fin c) := seq
  (CompactComplexSpectatorVolumeHandoff.program (s:=10+s) headerCount true
    ⟨7,by omega⟩ ⟨8,by omega⟩ (by intro h;have hv := congrArg Fin.val h;norm_num at hv) selected)
  (extend (CompactComplexControllerAlignedCommit.program (s:=s) (c:=c)) 10)

/-- Stream-volume synthesis and its erasure surround real spectator promotion.
The common header is committed after all role arrays have the new grid. -/
theorem raw_runs (sh : Shape) (headerCount rows ell metadataP : ℕ)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho : Fin sh.chunk) {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/headerCount) ell)
    (p C n : ℕ) (hp : p≤metadataP-2*sh.bits)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hwidth : ∀ j,Width sh (rows/headerCount) ell (metadataP-2*sh.bits) (before j))
    (hbefore : ∀ j,Grid sh (rows/headerCount) ell (metadataP-2*sh.bits) n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before j))
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
      rho path.visit dir selected before
    ∃ time,
      HoareTime (rawProgram (s:=s) headerCount selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage
          (CompactComplexStoppedGridHandoff.childPayload sh (rows/headerCount) ell (metadataP-2*sh.bits)
            rho path.visit dir selected source head before)))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready
          (bank control queue scalar old tail (committed storage (n+arity^k))
            (CompactComplexStoppedGridHandoff.payload sh (rows/headerCount) ell source head after))) time ∧
      time≤ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount true) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh headerCount rows ell metadataP true+8*(n+arity^k)+360)+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+3+
        (2*(bits n).length+4*(bits (n+arity^k)).length+15) ∧
      (∀ j,Grid sh (rows/headerCount) ell (metadataP-2*sh.bits) (n+arity^k)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^k))) (after j)) ∧
      (∀ j,j≠selected → decoded sh (rows/headerCount) ell (metadataP-2*sh.bits) (n+arity^k) (after j)=
        decoded sh (rows/headerCount) ell (metadataP-2*sh.bits) n (before j)) := by
  dsimp only
  obtain ⟨time,hhand,hbound,_,hgrid,hvalues⟩ := CompactComplexSpectatorVolumeHandoff.handoff_runs
    sh headerCount rows ell metadataP true hc hr hgroup hG hA hK hmetadata rho path dir selected before
    p C n hp hchunk hwidth hbefore (⟨7,by omega⟩ : Fin (10+s)) ⟨8,by omega⟩
    (by intro h;have hv := congrArg Fin.val h;norm_num at hv) control queue scalar tail storage source head
    rawLeft rawCount slots right src dst hcurrent htarget
  let after := CompactComplexChildGridPromoted.aligned sh (rows/headerCount) ell (metadataP-2*sh.bits)
    rho path.visit dir selected before
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
  refine ⟨time+1+(2*(bits n).length+4*(bits (n+arity^k)).length+15),hrun,?_,hgrid,hvalues⟩
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

abbrev publicTapes (s c : ℕ) := permanentTapes (10+s) c
abbrev childTapes (s : ℕ) := CompactComplexStoppedCodecCaller.childTapes (10+s)
abbrev targetTapes (s : ℕ) := CompactComplexStoppedLedgerRoundtrip.privateTapes s
abbrev privateTapes (s c : ℕ) := publicTapes s c+10
abbrev tapes (s c : ℕ) := (((publicTapes s c+86)+childTapes s)+targetTapes s)+privateTapes s c

def ready (v : Tapes (publicTapes s c) 2) : Tapes (tapes s c) 2 :=
  (frame v 86 (childTapes s) (targetTapes s)).append (SharedBank.empty (privateTapes s c) 2)
private def codecExtend {r : ℕ} (M : Program (publicTapes s c+86) r 2) :=
  extend (extend (extend M (childTapes s)) (targetTapes s)) (privateTapes s c)
def alignmentProgram (m s c : ℕ) (selected : Fin c) := seq (seq
  (codecExtend (CompactComplexNativeCodecFrame.program c m (10+s)))
  (adapt (rawProgram (s:=s) c selected) 86 (childTapes s) (targetTapes s)))
  (codecExtend (CompactComplexNativeCodecFrame.cleanupProgram (10+s) c))

attribute [local irreducible] CompactComplexSpectatorTargetFamily.compile rawProgram
  CompactComplexNativeCodecFrame.program CompactComplexNativeCodecFrame.cleanupProgram adapt codecExtend

/-- The parent metadata starts and ends at the original thirteen headers.
Original descriptors regenerate precision, volume27 is generated physically,
spectators align, the live denominator is installed, and all work is blank. -/
theorem alignment_runs (sh : Shape) (m d D G K0 ell q rows : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K0) (hrow : CompactGlobalRowPadding.rowAxes c m d≤D) (hDp : 0<D)
    (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunkPos : 0<sh.chunk)
    (rho : Fin sh.chunk) (v : ActivePrefixStageParameters.Stage sh) (hrho : v.rho=rho.val)
    {left k levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (p C n : ℕ)
    (hmetadata : 2*sh.bits≤CompactNativeRoleReservedBridge.precision c m d D K0 q)
    (hp : p≤CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hwidth : ∀ j,Width sh (rows/c) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits) (before j))
    (hbefore : ∀ j,Grid sh (rows/c) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits) n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before j))
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
      rho path.visit dir selected before
    ∃ time,
      HoareTime (alignmentProgram m s c selected)
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail storage
          (CompactComplexStoppedGridHandoff.childPayload sh (rows/c) ell (metadataP-2*sh.bits)
            rho path.visit dir selected (fun _ => blank) 0 before)))
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail
          (committed storage (n+arity^k)) (CompactComplexStoppedGridHandoff.payload sh (rows/c) ell (fun _ => blank) 0 after))) time ∧
      time≤CompactComplexNativeCodec.prepareCost c m D K0 rho.val ell q d G+
        (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true) old+
          (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
            (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+8*(n+arity^k)+360)+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+3+
          (2*(bits n).length+4*(bits (n+arity^k)).length+15))+
        CompactComplexNativeCodec.cleanupCost ell metadataP+2 ∧
      (∀ j,Grid sh (rows/c) ell (metadataP-2*sh.bits) (n+arity^k)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^k))) (after j)) ∧
      (∀ j,j≠selected → decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+arity^k) (after j)=
        decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before j)) := by
  dsimp only
  let metadataP := CompactNativeRoleReservedBridge.precision c m d D K0 q
  let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
  let start := CompactComplexStoppedGridHandoff.childPayload sh (rows/c) ell (metadataP-2*sh.bits)
    rho path.visit dir selected (fun _ => blank) 0 before
  let after := CompactComplexChildGridPromoted.aligned sh (rows/c) ell (metadataP-2*sh.bits)
    rho path.visit dir selected before
  let output := CompactComplexStoppedGridHandoff.payload sh (rows/c) ell (fun _ => blank) 0 after
  have hprepare := CompactComplexNativeCodecFrame.prepare_runs c m D K0 rho.val ell q d G hc hm hd hK hrow hDp
    v rows control queue tail storage start
  have hprepare' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hprepare
    (SharedBank.empty (childTapes s) 2)) (SharedBank.empty (targetTapes s) 2))
    (SharedBank.empty (privateTapes s c) 2)
  obtain ⟨time,hraw,hbound,hgrid,hvalues⟩ := raw_runs sh c rows ell metadataP (by omega) hr hgroup
    hG hA hchunkPos hmetadata rho path dir selected before p C n hp hchunk hwidth hbefore
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
    CompactComplexNativeCodec.cleanupCost ell metadataP,?_,?_,hgrid,hvalues⟩
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

def roundtripAllowance {sh : Shape} (m d D K0 ell q n : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows : ℕ) :=
  let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
  CompactComplexControllerChildStopTarget.cost d (k+2) n (arity^(k+1))+
    (4*(bits targetN).length+13+CompactComplexControllerChildBudget.entryCost
      Networks.ComplexRecursiveCallSchema.sites.length rho visit ha pair call.slot rows)+
    CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1))+
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+3+
      (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot+2*(bits targetN).length+8))+3

def alignmentAllowance (sh : Shape) (c m d D G K0 ell q rows n k : ℕ)
    (rho : Fin sh.chunk) (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c) :=
  let metadataP := CompactNativeRoleReservedBridge.precision c m d D K0 q
  CompactComplexNativeCodec.prepareCost c m D K0 rho.val ell q d G+
    (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
      (CompactComplexNativeCodec.raw v rows ell metadataP)+
      (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
        (130*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+8*(n+arity^k)+360)+
      ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
        (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho.val v.left v.f v.slots v.right v.source.val v.target.val)+3+
      (2*(bits n).length+4*(bits (n+arity^k)).length+15))+
    CompactComplexNativeCodec.cleanupCost ell metadataP+2

def program (m s : ℕ) (headerStack pcStack : Fin s) (call : Call) := seq
  (extend (CompactComplexStoppedLedgerRoundtrip.program m s headerStack pcStack call) (privateTapes s roleCount))
  (alignmentProgram m s roleCount (role call.site))

attribute [local irreducible] roleCount role alignmentProgram CompactComplexStoppedLedgerRoundtrip.program
  CompactComplexNativeRoleBridge.single CompactNativeRoleGuardedChildCaller.setRole
  CompactNativeRoleReservedBridge.rolePayload CompactNativeRoleReservedBridge.role
  CompactNativeRoleSourcePorts.roles CompactComplexStoppedGridHandoff.childPayload
  CompactComplexStoppedGridHandoff.payload CompactComplexChildGridPromoted.aligned
  Networks.ComplexPhaseBudget.edges

/-- The actual stopped call, physical spectator-grid handoff and live commit
form one fixed program. The output contains the exact aligned role arrays at
the installed leaf denominator, with every old frame and all work restored. -/
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
    (pBase C : ℕ) (hC : 1≤C) (hpBase : pBase≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤K0)
    (hfgrid : Grid (CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt CompactComplexRolePhaseSite.roleCount m d K0 level) ell
      (CompactNativeRoleReservedBridge.precision CompactComplexRolePhaseSite.roleCount m d D K0 q-
        2*(CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount m d D G K0).bits) n
      (CompactRecursiveGridBudget.bound pBase C levels (frames+2*returned)) f) :
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
        alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 ∧
      (∀ j,Grid sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN
        (CompactRecursiveGridBudget.bound pBase C (levels+1)
          ((frames+arity^(k+2))+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)+arity^(k+1))))
        (after j)) ∧
      (∀ j,j≠role call.site → decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN (after j)=
        decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) n (before j)) := by
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
  have hp : pBase≤metadataP-2*sh.bits := by
    dsimp only [sh,metadataP]
    rw [hprecision.2]
    omega
  have hc : 2≤roleCount := by unfold roleCount;norm_num
  have hr : 0<rows := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by omega) hK (by omega)
  have hgroup : 0<rows/roleCount := CompactComplexStoppedGridHandoff.reserved_rows_pos rows (by omega) hr hdiv
  have hglobal : Grid sh rows ell (metadataP-2*sh.bits) n
      (CompactRecursiveGridBudget.bound pBase C (levels+1)
        ((frames+arity^(k+2))+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)))) f := by
    intro i
    exact Networks.GaussianPrecision.bound_mono (child_budget path call pBase C hC) (hfgrid i)
  have hwidth := reserved_width sh rows ell metadataP hdiv hmetadata f hw
  have hroles := CompactComplexStoppedGridHandoff.reserved_grid sh rows ell (metadataP-2*sh.bits) n _ hdiv f hglobal
  have hrow : CompactGlobalRowPadding.rowAxes roleCount m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD;omega
  have hcur := CompactComplexStoppedLedgerRoundtrip.live_frame storage targetN
  have htar := CompactComplexStoppedLedgerRoundtrip.targeted_ready storage targetN
  obtain ⟨alignmentTime,halign,halignBound,hgrid,hvalues⟩ := alignment_runs sh m d D G K0 ell q rows hc hm
    hd hK hrow hDp hr hgroup hG hd hK rho parent rfl (Path.child path call)
    (CompactComplexStoppedCallSite.direction call) (role call.site) before pBase C n
    hmetadata hp hchunk hwidth hroles (ActiveRepairRankHeadersCommands.bank st) queue tail
    (CompactComplexStoppedLedgerRoundtrip.targeted storage targetN)
    ⟨hcur.1.trans hn.2,hcur.2.trans hn.1⟩ htar
  rw [reserved_child sh rows ell metadataP hdiv rho (Visit.child path.visit call.slot)
    (CompactComplexStoppedCallSite.direction call) (role call.site) f] at halign
  rw [←show targetN=n+arity^(k+1) from rfl,committed_targeted storage targetN] at halign
  have hroundtrip' := hoare_extend_eq hroundtrip (SharedBank.empty (privateTapes s roleCount) 2)
  have hrun := hroundtrip'.seq halign
  refine ⟨hdiv,roundtripTime+1+alignmentTime,?_,?_,hgrid,hvalues⟩
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

end
end IntegerMultBounds.Machine.CompactComplexStoppedAlignedCall
