import IntegerMultBounds.Machine.CompactComplexControllerExactReturn
import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeBudget
import IntegerMultBounds.Machine.CompactComplexDenominatorCapacity

/-! All generated exact-return headers, all permanent-role contractions and
the live commit have uniform original native and role-stream costs. The upper
true-live ledger supplies capacity; completed-network semantics remains honest. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactRecursiveDependencyBudget (Path)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSpectatorVolumeHeaders
open CompactNativeRoleTransferBudget (volume)
open CompactComplexControllerExactReturn
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

private theorem family_commit_linear (c V current target : ℕ)
    (hV : 0<V) (hc : current≤V) (ht : target≤current) :
    c*(129*V+8*current+360)+(2*(bits current).length+4*(bits target).length+15)+3≤(497*c+30)*V := by
  have h0 := ActiveRepairRankHeadersCommands.bits_length current
  have h1 := ActiveRepairRankHeadersCommands.bits_length target
  have hm := Nat.mul_le_mul_left c (show 129*V+8*current+360≤137*V+360 by omega)
  have hf := Nat.mul_le_mul_left (360*c+24) (show 1≤V by omega)
  nlinarith

def nativeConstant (headerCount c : ℕ) := CompactComplexSpectatorVolumeBudget.constant headerCount+497*c+30

def roleConstant (headerCount c : ℕ) := CompactComplexSpectatorVolumeBudget.streamConstant headerCount+497*c+30

theorem stream_le_native (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool) :
    streamVolume sh headerCount rows ell metadataP merge≤volume rows sh ell metadataP := by
  have hrows : roleRows headerCount rows merge≤rows := by
    cases merge
    · exact le_rfl
    · exact Nat.div_le_self rows headerCount
  have h := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell metadataP) hrows
  simpa only [streamVolume,volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
    CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using h

/-- The actual upper live-progress invariant discharges the signed return
capacity, rather than treating the true denominator as stored metadata. -/
theorem current_capacity {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned) (R base q usedRows current : ℕ)
    (hb : base≤q) (hu : usedRows≤R) (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    current≤CompactSpectatorInheritedGrid.half sh q :=
  CompactComplexDenominatorCapacity.target_capacity path R base q usedRows current current hb hu hroom hlive
    (Nat.le_add_right _ _)

/-- Both denominator lengths and all role-return scans are paid from one
actual serialized complete role, including both signed components. -/
theorem family_cost_from_path {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hgroup : 0<rows/headerCount) (hr : 0<rows) (hmetadata : 2*sh.bits≤metadataP)
    (R base usedRows current target c : ℕ)
    (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (ht : target≤current) :
    c*(129*streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
      (2*(bits current).length+4*(bits target).length+15)+3≤
        (497*c+30)*streamVolume sh headerCount rows ell metadataP merge := by
  have hrows : 0<roleRows headerCount rows merge := by cases merge <;> assumption
  have hcur := CompactComplexDenominatorCapacity.target_volume path R base (metadataP-2*sh.bits)
    usedRows current current (roleRows headerCount rows merge) ell hb hu hroom hlive
    (Nat.le_add_right _ _) hrows
  rw [←volume_semantic sh headerCount rows ell metadataP merge hmetadata] at hcur
  have hV : 0<streamVolume sh headerCount rows ell metadataP merge := by
    unfold streamVolume
    positivity
  exact family_commit_linear c _ current target hV hcur ht

theorem raw_cost_native {sh : Shape} {pathLeft k levels frames returned : ℕ}
    (path : Path sh.active pathLeft k levels frames returned)
    (headerCount rows ell metadataP rho left count slots right src dst : ℕ) (merge : Bool)
    (hgroup : 0<rows/headerCount) (hr : 0<rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (R base usedRows current target c : ℕ)
    (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (ht : target≤current) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
    ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
      c*(129*streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
      ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+
      (2*(bits current).length+4*(bits target).length+15)+3≤
        nativeConstant headerCount c*volume rows sh ell metadataP := by
  dsimp only
  have hh := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh headerCount rows ell metadataP
    rho left count slots right src dst merge hr hA hG hK
  have hf := family_cost_from_path path headerCount rows ell metadataP merge hgroup hr hmetadata
    R base usedRows current target c hb hu hroom hlive ht
  have hm := Nat.mul_le_mul_left (497*c+30) (stream_le_native sh headerCount rows ell metadataP merge)
  unfold nativeConstant
  nlinarith only [hh,hf,hm]

theorem raw_cost_role {sh : Shape} {pathLeft k levels frames returned : ℕ}
    (path : Path sh.active pathLeft k levels frames returned)
    (headerCount rows ell metadataP rho left count slots right src dst : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hgroup : 0<rows/headerCount) (hr : 0<rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (R base usedRows current target c : ℕ)
    (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (ht : target≤current) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
    ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
      c*(129*streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
      ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+
      (2*(bits current).length+4*(bits target).length+15)+3≤
        roleConstant headerCount c*streamVolume sh headerCount rows ell metadataP merge := by
  dsimp only
  have hh := CompactComplexSpectatorVolumeBudget.setup_cleanup_stream sh headerCount rows ell metadataP
    rho left count slots right src dst merge hcount hr hgroup hA hG hK
  have hf := family_cost_from_path path headerCount rows ell metadataP merge hgroup hr hmetadata
    R base usedRows current target c hb hu hroom hlive ht
  unfold roleConstant
  nlinarith only [hh,hf]

/-- Genuine padded descendant volume is paid by twice the original unpadded
native stream, uniformly across retained recursive row levels. -/
theorem original_volume (c m d D G K0 ell q level : ℕ) (hc : 0<c) (hK : 0<K0)
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

theorem realizes_weaken {t : ℕ} {P : Σ q,Program (t+10) q 2}
    {v0 v1 : Tapes t 2} {A B : ℕ} (h : Realizes P v0 v1 A) (hAB : A≤B) :
    Realizes P v0 v1 B := h.consequence (fun _ hz => hz) (fun _ hz => hz) hAB

open NativeSignedGapReturn (word)
open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision (BoundedGrid)
attribute [local irreducible] CompactComplexExactReturnFamily.compile program

theorem raw_runs_native_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current target : ℕ) (hle : target≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage target) (CompactComplexControllerExactReturn.returned ws current target payload))
      (nativeConstant headerCount c*volume rows sh ell metadataP) := by
  dsimp only
  have hcap := current_capacity path R base (metadataP-2*sh.bits) usedRows current hb hu hroom hlive
  have hcapacity : current-target≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 :=
    (Nat.sub_le _ _).trans (hcap.trans (Nat.le_succ _))
  have hrun := CompactComplexControllerExactReturn.raw_runs sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current target hle hcapacity hc ht hs
  have hcost := raw_cost_native path headerCount rows ell metadataP rho left count slots right src dst merge
    hgroup hr hG hA hK hmetadata R base usedRows current target c hb hu hroom hlive hle
  have hnew := realizes_weaken hrun hcost
  exact hnew

theorem nonleaf_runs_native_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current n k M : ℕ)
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits (CompactComplexDenominatorPolicy.networkTarget n k)))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size (roleRows headerCount rows merge) sh.bits (2^ell)) →
      Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage (CompactComplexDenominatorPolicy.networkTarget n k)) (CompactComplexControllerExactReturn.returned ws current (CompactComplexDenominatorPolicy.networkTarget n k) payload))
      (nativeConstant headerCount c*volume rows sh ell metadataP) ∧
    ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i) := by
  dsimp only
  have hcap := current_capacity path R base (metadataP-2*sh.bits) usedRows current hb hu hroom hlive
  have hcapacity : current-CompactComplexDenominatorPolicy.networkTarget n k≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 :=
    (Nat.sub_le _ _).trans (hcap.trans (Nat.le_succ _))
  have horder := CompactComplexDenominatorPolicy.network_target_le_current n k current hledger
  obtain ⟨hrun,hexact⟩ := CompactComplexControllerExactReturn.nonleaf_runs sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current n k M hledger hcapacity hc ht hs roles addresses original hg hcompleted
  have hcost := raw_cost_native path headerCount rows ell metadataP rho left count slots right src dst merge
    hgroup hr hG hA hK hmetadata R base usedRows current (CompactComplexDenominatorPolicy.networkTarget n k) c hb hu hroom hlive horder
  have hnew := realizes_weaken hrun hcost
  exact ⟨hnew,hexact⟩

theorem raw_runs_role_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current target : ℕ) (hle : target≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage target) (CompactComplexControllerExactReturn.returned ws current target payload))
      (roleConstant headerCount c*streamVolume sh headerCount rows ell metadataP merge) := by
  dsimp only
  have hcap := current_capacity path R base (metadataP-2*sh.bits) usedRows current hb hu hroom hlive
  have hcapacity : current-target≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 :=
    (Nat.sub_le _ _).trans (hcap.trans (Nat.le_succ _))
  have hrun := CompactComplexControllerExactReturn.raw_runs sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current target hle hcapacity hc ht hs
  have hcost := raw_cost_role path headerCount rows ell metadataP rho left count slots right src dst merge
    hcount hgroup hr hG hA hK hmetadata R base usedRows current target c hb hu hroom hlive hle
  have hnew := realizes_weaken hrun hcost
  exact hnew

theorem nonleaf_runs_role_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current n k M : ℕ)
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits (CompactComplexDenominatorPolicy.networkTarget n k)))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size (roleRows headerCount rows merge) sh.bits (2^ell)) →
      Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage (CompactComplexDenominatorPolicy.networkTarget n k)) (CompactComplexControllerExactReturn.returned ws current (CompactComplexDenominatorPolicy.networkTarget n k) payload))
      (roleConstant headerCount c*streamVolume sh headerCount rows ell metadataP merge) ∧
    ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i) := by
  dsimp only
  have hcap := current_capacity path R base (metadataP-2*sh.bits) usedRows current hb hu hroom hlive
  have hcapacity : current-CompactComplexDenominatorPolicy.networkTarget n k≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 :=
    (Nat.sub_le _ _).trans (hcap.trans (Nat.le_succ _))
  have horder := CompactComplexDenominatorPolicy.network_target_le_current n k current hledger
  obtain ⟨hrun,hexact⟩ := CompactComplexControllerExactReturn.nonleaf_runs sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current n k M hledger hcapacity hc ht hs roles addresses original hg hcompleted
  have hcost := raw_cost_role path headerCount rows ell metadataP rho left count slots right src dst merge
    hcount hgroup hr hG hA hK hmetadata R base usedRows current (CompactComplexDenominatorPolicy.networkTarget n k) c hb hu hroom hlive horder
  have hnew := realizes_weaken hrun hcost
  exact ⟨hnew,hexact⟩

end
end IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
