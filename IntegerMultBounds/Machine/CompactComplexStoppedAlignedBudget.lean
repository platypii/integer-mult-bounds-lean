import IntegerMultBounds.Machine.CompactComplexStoppedAlignedCall
import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeBudget
import IntegerMultBounds.Machine.CompactComplexDenominatorCapacity

/-! Actual stopped alignment costs, including all generated metadata, are
paid from original native volume under the true live-progress invariant. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
variable {s : ℕ}
open CompactComplexStoppedAlignedCall
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] Networks.ComplexPhaseBudget.edges
  alignmentAllowance
  CompactComplexControllerChildBudget.entryCost CompactComplexControllerChildBudget.returnCost
  CompactComplexControllerChildStopTarget.cost
  CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites
  CompactComplexStoppedCodecCaller.constant CompactComplexChildHeadersUniform.constant

def codecConstant (c m : ℕ) := CompactReservationPaddingHeaderBudget.constant c m+5000

def nativeConstant (c : ℕ) := CompactComplexSpectatorVolumeBudget.constant c+498*c+32

theorem stream_le_native (sh : Shape) (c rows ell metadataP : ℕ) :
    streamVolume sh c rows ell metadataP true≤volume rows sh ell metadataP := by
  have h := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell metadataP) (Nat.div_le_self rows c)
  simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,ite_true,
    volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
    CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using h

theorem spectator_count {c : ℕ} (selected : Fin c) :
    (CompactComplexSpectatorPromoteFamily.spectatorList selected).length≤c := by
  exact (List.length_filter_le _ _).trans (by simp)

/-- Both actual header schedules and physical promotion/commit are charged;
the sole denominator premise is the recursive true-live progress invariant. -/
theorem alignment_allowance_native (sh : Shape) (c m d D G K0 ell q rows n : ℕ)
    (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (hshapeG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (hr : 0<rows) (hgroup : 0<rows/c)
    (rho : Fin sh.chunk) (v : ActivePrefixStageParameters.Stage sh) (hrho : v.rho=rho.val)
    {left k levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (selected : Fin c)
    (hmetadata : 2*sh.bits≤CompactNativeRoleReservedBridge.precision c m d D K0 q)
    (R base usedRows : ℕ)
    (hbase : base≤CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits)
    (hprefix : usedRows≤R) (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : Width sh (rows/c) ell (CompactNativeRoleReservedBridge.precision c m d D K0 q-2*sh.bits) f) :
    alignmentAllowance sh c m d D G K0 ell q rows n k rho v selected≤
      codecConstant c m*CompactFallbackAxisRun.volume D K0 ell q+
        nativeConstant c*volume rows sh ell (CompactNativeRoleReservedBridge.precision c m d D K0 q) := by
  let metadataP := CompactNativeRoleReservedBridge.precision c m d D K0 q
  let V := volume rows sh ell metadataP
  let W := streamVolume sh c rows ell metadataP true
  have hcodec := CompactComplexNativeCodec.lifecycle_linear c m D K0 rho.val ell q d G hc hm hd hG hK hD
  have hraw : CompactComplexNativeCodec.raw v rows ell metadataP=
      CompactSpectatorLeafSetup.raw sh rows ell metadataP rho.val v.left v.f v.slots v.right v.source.val v.target.val := by
    unfold CompactComplexNativeCodec.raw CompactNativeRoleConjugatedLifecycle.rawState
    rw [hrho]
  have hheaders := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    rho.val v.left v.f v.slots v.right v.source.val v.target.val true hr hA hshapeG hchunk
  rw [←hraw] at hheaders
  have hpromotion := CompactComplexDenominatorCapacity.cost_from_path path R base (metadataP-2*sh.bits)
    usedRows n (n+arity^k) (rows/c) ell
    (CompactComplexSpectatorPromoteFamily.spectatorList selected).length hbase hprefix hroom hlive
    (by omega) (by omega) hgroup f hw
  dsimp only at hpromotion
  have hvolume := CompactComplexSpectatorVolumeHeaders.volume_semantic sh c rows ell metadataP true hmetadata
  simp only [CompactComplexSpectatorVolumeHeaders.roleRows,ite_true] at hvolume
  rw [CompactComplexStoppedGridHandoff.words_volume sh (rows/c) ell (metadataP-2*sh.bits) f hw,
    ←hvolume] at hpromotion
  have hcount := spectator_count selected
  have hW : W≤V := stream_le_native sh c rows ell metadataP
  have hpos : 0<V := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hpromo : (498*(CompactComplexSpectatorPromoteFamily.spectatorList selected).length+28)*W≤(498*c+28)*V :=
    Nat.mul_le_mul (by omega) hW
  unfold alignmentAllowance nativeConstant codecConstant
  change _≤_ at hheaders hpromotion hcodec
  dsimp only [metadataP,V,W] at hW hpos hpromo
  nlinarith

private theorem stop_argument (d e n gap V : ℕ) (hd : d+1≤4*V)
    (he : e≤d+1) (ht : n+gap≤V) (_hV : 0<V) : d+e+n+gap+1≤11*V := by omega

private theorem bits_twice (n V : ℕ) (hn : n≤V) (hV : 0<V) : (bits n).length≤2*V := by
  have h := ActiveRepairRankHeadersCommands.bits_length n
  omega

private theorem control_sum (stop entry ret addr len V child A T : ℕ)
    (hs : stop≤T*(11*V)) (hc : entry+addr+5+ret+2≤A*V)
    (hl : len≤2*V) (hV : 0<V) :
    stop+(4*len+13+entry)+child+(addr+3+(ret+2*len+8))+3≤(A+11*T+32)*V+child := by
  nlinarith

@[irreducible] def controllerConstantFor (siteCount : ℕ) :=
  4*(CompactComplexChildHeadersUniform.constant+
    2*CompactComplexCallReturn.addressWidth siteCount arity+212)+
      11*CompactComplexControllerChildStopTarget.timeConstant+32

def controllerConstant := controllerConstantFor Networks.ComplexRecursiveCallSchema.sites.length

private theorem controller_for_eq (siteCount : ℕ) : controllerConstantFor siteCount=
  4*(CompactComplexChildHeadersUniform.constant+
    2*CompactComplexCallReturn.addressWidth siteCount arity+212)+
      11*CompactComplexControllerChildStopTarget.timeConstant+32 := by
  unfold controllerConstantFor
  rfl

private theorem roundtrip_eq {sh : Shape} (m d D K0 ell q n : ℕ)
    (rows : ℕ)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    roundtripAllowance (sh:=sh) m d D K0 ell q n rho visit ha pair call rows=CompactComplexControllerChildStopTarget.cost d (k+2) n (arity^(k+1))+
        (4*(bits (n+arity^(k+1))).length+13+
          CompactComplexControllerChildBudget.entryCost Networks.ComplexRecursiveCallSchema.sites.length rho visit ha pair call.slot rows)+
        CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*arity^(k+1)+
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+3+
          (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot+2*(bits (n+arity^(k+1))).length+8))+3 := by rfl


private theorem controller_constant_eq : controllerConstant=
  4*(CompactComplexChildHeadersUniform.constant+
    2*CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+212)+
      11*CompactComplexControllerChildStopTarget.timeConstant+32 :=
  controller_for_eq Networks.ComplexRecursiveCallSchema.sites.length

attribute [local irreducible] controllerConstant roundtripAllowance

/-- Actual stopped dispatch, target-stack traffic and return-controller work
are charged directly, rather than supplied as a metadata allowance. -/
theorem roundtrip_allowance_native {sh : Shape} (m d D K0 ell q n metadataP : ℕ)
    (haxes : sh.axes=d) (rows : ℕ) (hr : 0<rows) (hG : 1≤sh.guard)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (htarget : n+arity^(k+1)≤volume rows sh ell metadataP) :
    roundtripAllowance (sh:=sh) m d D K0 ell q n rho visit ha pair call rows≤
      controllerConstant*volume rows sh ell metadataP+
        CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) := by
  let V := volume rows sh ell metadataP
  have hV : 0<V := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hdim := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=sh) rows ell metadataP hr hG
  have hsmall : sh.axes+1≤(sh.axes+1)^2 := by nlinarith only []
  have he := CompactComplexControllerChildBudget.exponent_bound visit ha
  have hcontrol := CompactComplexControllerChildBudget.lifecycle_linear (s:=sh) Networks.ComplexRecursiveCallSchema.sites.length
    rho visit ha pair call.slot rows ell metadataP hr hG
  have hstop := CompactComplexControllerChildStopTarget.cost_le d (k+2) n (arity^(k+1))
  have hdV : d+1≤4*V := by rw [←haxes];exact hsmall.trans hdim
  have heV : k+2≤d+1 := by rw [←haxes];exact (Nat.le_succ _).trans he
  have harg := stop_argument d (k+2) n (arity^(k+1)) V hdV heV htarget hV
  have hs := hstop.trans (Nat.mul_le_mul_left CompactComplexControllerChildStopTarget.timeConstant harg)
  have hbits := bits_twice (n+arity^(k+1)) V htarget hV
  have hfirst := roundtrip_eq (sh:=sh) m d D K0 ell q n rows rho visit ha pair call
  have h := control_sum
    (CompactComplexControllerChildStopTarget.cost d (k+2) n (arity^(k+1)))
    (CompactComplexControllerChildBudget.entryCost Networks.ComplexRecursiveCallSchema.sites.length
      rho visit ha pair call.slot rows)
    (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot)
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity)
    (bits (n+arity^(k+1))).length (volume rows sh ell metadataP)
    (CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*arity^(k+1))
    (4*(CompactComplexChildHeadersUniform.constant+
      2*CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+212))
    CompactComplexControllerChildStopTarget.timeConstant hs hcontrol hbits hV
  exact hfirst.le.trans (h.trans (le_of_eq (congrArg
    (fun a => a*volume rows sh ell metadataP+
      CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*arity^(k+1))
    controller_constant_eq.symm)))

/-- The actual padded descendant native volume is at most twice the original
unpadded native stream. No row-volume budget is assumed. -/
theorem actual_native_volume (c m d D G K0 ell q level : ℕ) (hc : 0<c) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D) :
    volume (CompactGlobalRowPadding.rowsAt c m d K0 level)
      (CompactReservationNativeRows.shape c m d D G K0) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q)≤
        2*CompactFallbackAxisRun.volume D K0 ell q := by
  have hrow := Nat.mul_le_mul_right
    (CompactNativeRoleOriginal.symbols (CompactReservationNativeRows.shape c m d D G K0) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q))
    (CompactGlobalRowPadding.rowsAt_le_initial c m d K0 level)
  exact hrow.trans (CompactNativeRoleTransferBudget.reservation_volume c m d D G K0 ell q hc hK hD)

theorem native_semantic (sh : Shape) (rows ell metadataP : ℕ) (hp : 2*sh.bits≤metadataP) :
    volume rows sh ell metadataP=
      ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*
        (2*(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2)) := by
  have h := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell metadataP false hp
  simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
    volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
    CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using h

open CompactComplexRolePhaseSite (roleCount role)
open Networks.ComplexRecursiveCallSchema (Call)

def constant (m : ℕ) := CompactComplexStoppedCodecCaller.constant m+codecConstant roleCount m+
  2*(nativeConstant roleCount+controllerConstant)+1

attribute [local irreducible] program ready alignmentProgram CompactComplexStoppedLedgerRoundtrip.program
  CompactComplexNativeRoleBridge.single CompactNativeRoleGuardedChildCaller.setRole
  CompactNativeRoleReservedBridge.rolePayload CompactNativeRoleReservedBridge.role
  CompactNativeRoleSourcePorts.roles CompactComplexStoppedGridHandoff.childPayload
  CompactComplexStoppedGridHandoff.payload CompactComplexChildGridPromoted.aligned

theorem actual_runs_linear (m d D G K0 ell q level : ℕ) (hm : 2≤m)
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
      (CompactRecursiveGridBudget.bound pBase C levels (frames+2*returned)) f)
    (R base usedRows : ℕ) (hbase : base≤q) (hprefix : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤K0)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
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
      time≤constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) ∧
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
  let V := CompactFallbackAxisRun.volume D K0 ell q
  let N := volume rows sh ell metadataP
  obtain ⟨hdiv,time,hrun,hbound,hgrid,hvalues⟩ := CompactComplexStoppedAlignedCall.actual_runs
    m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path hstop pair call
    headerStack pcStack hne st h1 queue tail storage n hn ht hw0 hbH hbP hb9 f hw pBase C hC hpBase hchunk hfgrid
  have hc : 2≤roleCount := by unfold roleCount;norm_num
  have hr : 0<rows := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by omega) hK (by omega)
  have hgroup : 0<rows/roleCount := CompactComplexStoppedGridHandoff.reserved_rows_pos rows (by omega) hr hdiv
  have hprecision := CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD
  have hmetadata : 2*sh.bits≤metadataP := hprecision.1
  have hbase' : base≤metadataP-2*sh.bits := by dsimp only [metadataP,sh];rw [hprecision.2];omega
  have hroom' : CompactComplexDenominatorCapacity.room R≤sh.chunk := hroom
  have htarget := CompactComplexDenominatorCapacity.target_volume path R base (metadataP-2*sh.bits)
    usedRows n (n+arity^(k+1)) rows ell hbase' hprefix hroom' hlive
    (by
      have hpow : arity^(k+1)≤arity^(k+2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega) hr
  rw [←native_semantic sh rows ell metadataP hmetadata] at htarget
  have hroundtrip := roundtrip_allowance_native m d D K0 ell q n metadataP rfl rows hr (by change 1≤G;omega)
    rho path.visit ha pair call htarget
  have hliveChild : n≤CompactComplexDenominatorCapacity.ledger R base (levels+1)
      (frames+arity^(k+2)) (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)) 0 := by
    apply CompactComplexDenominatorCapacity.child_entry R base levels frames returned usedRows n (k+1) call hprefix
    unfold CompactComplexDenominatorCapacity.ledger at hlive ⊢
    omega
  have hwidth := CompactComplexStoppedAlignedCall.reserved_width sh rows ell metadataP hdiv hmetadata f hw
  have halignment := alignment_allowance_native sh roleCount m d D G K0 ell q rows n hc hm hd hG hK hD
    hG hd hK hr hgroup rho parent rfl (Path.child path call) (role call.site)
    hmetadata R base 0 hbase' (by omega) hroom' hliveChild
    (CompactNativeRoleReservedBridge.role sh rows roleCount ell hdiv f (role call.site)) (hwidth (role call.site))
  have hNV : N≤2*V := actual_native_volume roleCount m d D G K0 ell q level (by omega) hK hD
  have hV : 0<V := ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have hgap : 1≤arity^(k+1) := Nat.one_le_pow _ _ (by decide)
  have hmul := Nat.mul_le_mul_left (nativeConstant roleCount+controllerConstant) hNV
  have hnonchild := Nat.mul_le_mul_right V
    (show codecConstant roleCount m+2*(nativeConstant roleCount+controllerConstant)+1≤
      (codecConstant roleCount m+2*(nativeConstant roleCount+controllerConstant)+1)*arity^(k+1) from
        Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨hdiv,time,hrun,?_,hgrid,hvalues⟩
  change time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
    alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 at hbound
  change _≤controllerConstant*N+CompactComplexStoppedCodecCaller.constant m*V*arity^(k+1) at hroundtrip
  change _≤codecConstant roleCount m*V+nativeConstant roleCount*N at halignment
  unfold constant
  nlinarith only [hbound,hroundtrip,halignment,hmul,hV,hnonchild]

end
end IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget
