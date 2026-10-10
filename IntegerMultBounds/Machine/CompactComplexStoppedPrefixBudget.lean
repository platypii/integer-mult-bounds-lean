import IntegerMultBounds.Machine.CompactComplexStoppedPrefixAlignedCall
import IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget

/-! The exact-prefix stopped event has the original uniform volume-times-child
runtime. True live-header capacity follows from its actual scalar-prefix ledger. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedPrefixBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexStoppedGridHandoff (payload)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Width Grid decoded dependencyCoefficient)
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexStoppedPrefixAlignedCall (program ready)
open CompactComplexStoppedAlignedCall (committed roundtripAllowance alignmentAllowance)
open CompactComplexStoppedAlignedBudget (codecConstant nativeConstant controllerConstant alignment_allowance_native
  roundtrip_allowance_native native_semantic actual_native_volume)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexRolePhaseSite (roleCount role)
open Networks.ComplexRecursiveCallSchema (Call)
variable {s : ℕ}

private opaque actualRowsData : {R : ℕ // R=CompactComplexDenominatorCapacity.scalarRows} :=
  ⟨CompactComplexDenominatorCapacity.scalarRows,rfl⟩

def actualRows := actualRowsData.val

theorem actualRows_eq : actualRows=CompactComplexDenominatorCapacity.scalarRows :=
  actualRowsData.property
attribute [local irreducible] Networks.ComplexPhaseBudget.edges program ready
  roleCount role
  Networks.ComplexFramedExecution.rows
  CompactFramedScalarGrid.rows CompactComplexDenominatorCapacity.scalarRows
  CompactComplexStoppedPrefixAlignedCall.alignmentProgram CompactComplexStoppedLedgerRoundtrip.program
  CompactComplexNativeRoleBridge.single CompactNativeRoleGuardedChildCaller.setRole
  CompactNativeRoleSourcePorts.roles CompactComplexStoppedGridHandoff.childPayload
  CompactNativeRoleReservedBridge.role CompactNativeRoleReservedBridge.rolePayload
  CompactComplexStoppedGridHandoff.payload CompactComplexChildGridPromoted.aligned
  roundtripAllowance alignmentAllowance controllerConstant
  CompactComplexControllerChildBudget.entryCost CompactComplexControllerChildBudget.returnCost
  CompactComplexControllerChildStopTarget.cost
  CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites
  CompactComplexStoppedCodecCaller.constant CompactComplexChildHeadersUniform.constant

theorem axes_child_reserve {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left (k+2) levels frames returned) (axes : ℕ)
    (haxes : axes≤sh.active) (hchunk : 2≤sh.chunk) : axes+arity^(k+1)≤sh.bits := by
  have hv := path.visit.fits
  have hp : arity^(k+1)≤arity^(k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := Nat.mul_le_mul_left sh.active hchunk
  unfold CompactGadgetReservationShape.Shape.bits
  omega

private theorem combine_cost (time rt al a b c d V N gap : ℕ)
    (ht : time≤rt+al+1) (hr : rt≤d*N+a*V*gap) (ha : al≤b*V+c*N)
    (hm : (c+d)*N≤(c+d)*(2*V)) (hV : 0<V)
    (hn : (b+2*(c+d)+1)*V≤(b+2*(c+d)+1)*V*gap) :
    time≤(a+b+2*(c+d)+1)*V*gap := by
  calc
    _ ≤ rt+al+1 := ht
    _ ≤ (d*N+a*V*gap)+(b*V+c*N)+1 := by omega
    _ = a*V*gap+b*V+(c+d)*N+1 := by ring
    _ ≤ a*V*gap+b*V+(c+d)*(2*V)+V := by omega
    _ = a*V*gap+(b+2*(c+d)+1)*V := by ring
    _ ≤ a*V*gap+(b+2*(c+d)+1)*V*gap := Nat.add_le_add_left hn _
    _ = _ := by ring

private theorem two_le_room (R : ℕ) : 2≤CompactComplexDenominatorCapacity.room R := by
  exact Nat.le_add_left 2 (R+CompactRecursiveDependencyBudget.volumeCoefficient)

theorem allowance_linear (m d D G K0 ell q level : ℕ) (hm : 2≤m)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0) (_hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (n : ℕ)
    (before : Fin roleCount → Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level/roleCount) ell)
    (hw : ∀ j i,(before j i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (before j i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q))
    (g : ℕ)
    (base : ℕ) (hbase : base≤q)
    (hliveRoom : CompactComplexDenominatorCapacity.room actualRows≤K0)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger actualRows
      base levels frames returned (CompactFramedScalarGrid.rows g).length) :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
    roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
      alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 ≤
        CompactComplexStoppedAlignedBudget.constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
  let V := CompactFallbackAxisRun.volume D K0 ell q
  let N := volume rows sh ell metadataP
  let time := roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
    alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1
  have hbound : time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
    alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 := le_rfl
  have hdiv : roleCount∣rows := CompactGlobalRowPadding.split_divides roleCount m d K0 level
    (by unfold roleCount;norm_num) hK hj
  let f := CompactComplexStoppedEventProgress.reserved sh rows roleCount ell hdiv before
  have hglobalWidth := CompactComplexStoppedEventProgress.reserved_width sh rows roleCount ell
    (CompactNativeRoleHeaders.recordWidth sh metadataP) hdiv before hw
  let R := actualRows
  let usedRows := (CompactFramedScalarGrid.rows g).length
  have hprefix : usedRows≤R := by
    rw [show R=CompactComplexDenominatorCapacity.scalarRows from actualRows_eq]
    exact CompactComplexDenominatorCapacity.actual_prefix g
  have hlive' : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows := hlive
  have hc : 2≤roleCount := by unfold roleCount;norm_num
  have hr : 0<rows := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by omega) hK (by omega)
  have hgroup : 0<rows/roleCount := CompactComplexStoppedGridHandoff.reserved_rows_pos rows (by omega) hr hdiv
  have hprecision := CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD
  have hmetadata : 2*sh.bits≤metadataP := hprecision.1
  have hbase' : base≤metadataP-2*sh.bits := by dsimp only [metadataP,sh];rw [hprecision.2];omega
  have hroom' : CompactComplexDenominatorCapacity.room R≤sh.chunk := hliveRoom
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
    unfold CompactComplexDenominatorCapacity.ledger at hlive' ⊢
    omega
  have hwidth := CompactComplexStoppedAlignedCall.reserved_width sh rows ell metadataP hdiv hmetadata f hglobalWidth
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
  have hnonchild' := hnonchild.trans_eq
    (Nat.mul_right_comm (codecConstant roleCount m+2*(nativeConstant roleCount+controllerConstant)+1)
      (arity^(k+1)) V)
  change time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
    alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 at hbound
  change _≤controllerConstant*N+CompactComplexStoppedCodecCaller.constant m*V*arity^(k+1) at hroundtrip
  change _≤codecConstant roleCount m*V+nativeConstant roleCount*N at halignment
  dsimp only [V] at hroundtrip halignment hmul hV hnonchild'
  unfold CompactComplexStoppedAlignedBudget.constant
  have hcombined := combine_cost time
    (roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows)
    (alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site))
    (CompactComplexStoppedCodecCaller.constant m)
    (codecConstant roleCount m) (nativeConstant roleCount) controllerConstant
    (CompactFallbackAxisRun.volume D K0 ell q) N (arity^(k+1))
    hbound hroundtrip halignment hmul hV hnonchild'
  dsimp only [time,ha,rows,sh,parent] at hcombined
  exact hcombined

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
    (haxes : axes≤(CompactReservationNativeRows.shape roleCount m d D G K0).active)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤K0)
    (hgrid : ∀ j,Grid (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level/roleCount) ell
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q-
        2*(CompactReservationNativeRows.shape roleCount m d D G K0).bits) n
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))) (before j))
    (base : ℕ) (hbase : base≤q)
    (hliveRoom : CompactComplexDenominatorCapacity.room actualRows≤K0)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger actualRows
      base levels frames returned (CompactFramedScalarGrid.rows g).length) :
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
      time≤CompactComplexStoppedAlignedBudget.constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) ∧
      (∀ j,Grid sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN
        (CompactFramedScalarGrid.bound g
          (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes)))
        (after j)) ∧
      (∀ j,j≠role call.site → decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN (after j)=
        decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) n (before j)) := by
  dsimp only
  have hK2 : 2≤K0 := by
    exact (two_le_room actualRows).trans hliveRoom
  have hreserve := axes_child_reserve
    (sh:=CompactReservationNativeRows.shape roleCount m d D G K0) path axes haxes hK2
  obtain ⟨time,hrun,hbound,hgrid',hvalues⟩ := CompactComplexStoppedPrefixAlignedCall.actual_prefix_from_roles
    m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path hstop pair call
    headerStack pcStack hne st h1 queue tail storage n hn ht hw0 hbH hbP hb9 before hw
    g p C axes hp hC hreserve hroom hgrid
  have hcost := allowance_linear m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path
    pair call n before hw g base hbase hliveRoom hlive
  dsimp only at hbound hcost
  have htime := hbound.trans hcost
  exact ⟨time,hrun,htime,hgrid',hvalues⟩

end
end IntegerMultBounds.Machine.CompactComplexStoppedPrefixBudget
