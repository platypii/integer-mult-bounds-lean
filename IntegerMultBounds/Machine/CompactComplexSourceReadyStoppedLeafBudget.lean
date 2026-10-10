import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeaf
import IntegerMultBounds.Machine.CompactNativeRoleStoppedChildBudget
import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
import IntegerMultBounds.Machine.CompactComplexControllerDenominatorTarget

/-! Full source-ready stopped costs are uniformly paid from actual native
volume and visit count. The dependency Path/live ledger pays real denominator
traffic, including target synthesis, commit and every lifecycle join. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafGuardOriginal (Direction)
open ButterflyAxisHeadersArithmetic (scheduleCost)
open RecursiveChildQuotientsConstant (bits)
variable {sh : Shape} {left k : ℕ}

def metadataConstant := 50000*(6*arity+50)+FixedBasePowerDescriptor.constant 2+1000000
def constant := metadataConstant+CompactSpectatorLeafGuardBudget.phaseConstant+100

/-- Both scalar and exponent-zero raw nodes have genuinely bounded metadata;
no fictitious positive-exponent Stage is used for scalar leaves. -/
theorem scalar_linear (rows ell p : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left k)
    (slots right src dst : ℕ) (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard)
    (hpay : sh.payload=1) (hslots : slots≤arity) (hright : right≤sh.active)
    (hsrc : src≤arity) (hdst : dst≤arity) :
    CompactSpectatorLeafSetupBudget.scalar sh rows ell p rho.val left (arity^k) slots right src dst≤
      (3*arity+20)*volume rows sh ell p := by
  have hN : 0<arity^k := pow_pos (by decide) _
  have hfit := visit.fits
  have hleft : left<sh.active := by omega
  obtain ⟨hH,_,hactive,hchunk,hrho,hleft',_,_⟩ :=
    CompactSpectatorLeafAxisBudget.descriptors sh rho.val left rho.isLt hleft
  obtain ⟨hb,hp,_,hpoly,_,_,_,hrows⟩ := CompactNativeRoleHeaderBudget.values_le sh rows ell p hr
  have hell : ell≤volume rows sh ell p := (Nat.lt_two_pow_self (n:=ell)).le.trans hpoly
  have haxes : sh.axes≤sh.H := Nat.le_mul_of_pos_right _ hG
  have hguard : sh.guard≤sh.H := by
    simpa only [Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm] using
      Nat.le_mul_of_pos_right sh.guard hA
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hslot := Nat.le_mul_of_pos_right arity hV
  unfold CompactSpectatorLeafSetupBudget.scalar
  rw [hpay]
  nlinarith only [hN,hfit,hH,hactive,hchunk,hrho,hleft',hb,hp,hell,hrows,haxes,hguard,
    hV,hslots,hright,hsrc,hdst,hslot]

theorem expanded_scalar_linear (rows ell p : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left k)
    (slots right src dst : ℕ) (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard)
    (hpay : sh.payload=1) (hslots : slots≤arity) (hright : right≤sh.active)
    (hsrc : src≤arity) (hdst : dst≤arity) :
    CompactSpectatorLeafSetupBudget.scalar (NativePolynomialStageShape.shape sh ell p)
      rows ell p rho.val left (arity^k) slots right src dst≤(3*arity+23)*volume rows sh ell p := by
  have h0 := scalar_linear rows ell p rho visit slots right src dst hr hA hG hpay hslots hright hsrc hdst
  have h1 := NativePolynomialStageHeaderBudget.payload_le sh rows ell p hr
  have he : CompactSpectatorLeafSetupBudget.scalar (NativePolynomialStageShape.shape sh ell p)
      rows ell p rho.val left (arity^k) slots right src dst+sh.payload=
    CompactSpectatorLeafSetupBudget.scalar sh rows ell p rho.val left (arity^k) slots right src dst+
      NativePolynomialStageShape.payload sh ell p := by
    dsimp [CompactSpectatorLeafSetupBudget.scalar,NativePolynomialStageShape.shape,Shape.bits,Shape.H,Shape.B,Shape.F]
    ring
  nlinarith

theorem cost_linear (dir : Direction) (rows ell p : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left k)
    (slots right src dst : ℕ) (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard)
    (hpay : sh.payload=1) (hp : 2*sh.bits≤p) (hslots : slots≤arity) (hright : right≤sh.active)
    (hsrc : src≤arity) (hdst : dst≤arity) :
    CompactComplexSourceReadyLeaf.cost dir sh rows ell p rho visit slots right src dst≤
      (metadataConstant+CompactSpectatorLeafGuardBudget.phaseConstant)*volume rows sh ell p*(arity^k) := by
  have hK : 0<sh.chunk := by have := rho.isLt;omega
  have hH : 0<sh.H := Nat.mul_pos hA hG
  have hS := scalar_linear rows ell p rho visit slots right src dst hr hA hG hpay hslots hright hsrc hdst
  have hE := expanded_scalar_linear rows ell p rho visit slots right src dst hr hA hG hpay hslots hright hsrc hdst
  have hg := CompactSpectatorLeafSetupBudget.geometry_cost sh rows ell p rho.val left (arity^k) slots right src dst hH hK
  have hge := CompactSpectatorLeafSetupBudget.geometry_cost (NativePolynomialStageShape.shape sh ell p)
    rows ell p rho.val left (arity^k) slots right src dst hH hK
  have hc := NativePolynomialStageHeaders.rest_cost_bound sh rows ell p rho.val left (arity^k) slots right src dst
  have hclean := NativePolynomialStageHeaders.restore_cost_bound sh rows ell p rho.val left (arity^k) slots right src dst
  have hprec := CompactNativeRoleChildLifecycleBudget.precision_rest_cost (NativePolynomialStageShape.shape sh ell p)
    rows ell p rho.val left (arity^k) slots right src dst hH hK
  have hpayload := NativePolynomialStageHeaderBudget.payload_le sh rows ell p hr
  have hvals := CompactNativeRoleHeaderBudget.values_le sh rows ell p hr
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hvals.2.2.2.1
  have hphase := CompactSpectatorLeafGuardBudget.phase_cost dir (NativePolynomialStageShape.shape sh ell p)
    rows ell (p-2*sh.bits) rho visit slots right src dst hG hA hr hslots hright hsrc hdst
    (CompactNativeRoleStoppedChildBudget.guard_payload sh ell p hp)
  rw [CompactNativeRoleStoppedChildBudget.guard_volume sh rows ell p hp] at hphase
  have hsaveP := CompactNativeRoleChildPrecisionSaved.cost_saved CompactNativeRoleChildPrecision.prepare
    (Or.inl rfl) (CompactSpectatorLeafSetup.raw (NativePolynomialStageShape.shape sh ell p)
      rows ell p rho.val left (arity^k) slots right src dst) sh.payload
  have hsaveR := CompactNativeRoleChildPrecisionSaved.cost_saved CompactNativeRoleChildPrecision.restore
    (Or.inr rfl) (CompactNativeRoleChildPrecision.baseline (NativePolynomialStageShape.shape sh ell p)
      rows ell p rho.val left (arity^k) slots right src dst) sh.payload
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hN : 0<arity^k := pow_pos (by decide) _
  have hVN := Nat.le_mul_of_pos_right (volume rows sh ell p) hN
  unfold CompactComplexSourceReadyLeaf.cost NativePolynomialStageHeaders.cost
  rw [NativePolynomialStageHeaders.prepared,hsaveP,hsaveR]
  simp only [NativePolynomialStageShape.bits] at hprec
  rw [hpay] at hc hclean
  have hm : scheduleCost CompactSpectatorLeafSetup.geometry
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) slots right src dst)+
      scheduleCost NativePolynomialStageHeaders.rest (CompactSpectatorLeafSetup.state 0 sh rows ell p rho.val left (arity^k) slots right src dst)+1+
      scheduleCost CompactNativeRoleChildPrecision.prepare (CompactSpectatorLeafSetup.raw (NativePolynomialStageShape.shape sh ell p) rows ell p rho.val left (arity^k) slots right src dst)+
      scheduleCost CompactNativeRoleChildPrecision.restore (CompactNativeRoleChildPrecision.baseline (NativePolynomialStageShape.shape sh ell p) rows ell p rho.val left (arity^k) slots right src dst)+
      scheduleCost NativePolynomialStageHeaders.restore (NativePolynomialStageHeaders.prepared sh rows ell p rho.val left (arity^k) slots right src dst)+4≤
        metadataConstant*volume rows sh ell p := by
    unfold metadataConstant
    nlinarith only [hg,hge,hS,hE,hc,hclean,hprec,hpayload,hvals.1,hvals.2.1,hvals.2.2.2.1,hV,hpow]
  have hlift := Nat.mul_le_mul_left metadataConstant hVN
  simp only [NativePolynomialStageHeaders.prepared] at hm
  simp only [Nat.mul_assoc] at hphase
  simp only [Nat.add_mul,Nat.mul_assoc]
  omega

/-- The actual input live ledger also pays the newly generated leaf target. -/
theorem target_native {levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (rows ell metadataP R base usedRows n : ℕ) (hr : 0<rows) (hP : 2*sh.bits≤metadataP)
    (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    CompactComplexDenominatorPolicy.leafTarget n k≤volume rows sh ell metadataP := by
  have ht := CompactComplexDenominatorCapacity.target_capacity path R base (metadataP-2*sh.bits)
    usedRows n (n+arity^k) hb hu hroom hlive (by omega)
  have hv := (CompactNativeRoleHeaderBudget.values_le sh rows ell metadataP hr).2.2.2.2.2.1
  unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at ht
  unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth at hv
  unfold CompactComplexDenominatorPolicy.leafTarget
  omega

def fullCost (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k) (slots right src dst n : ℕ) :=
  CompactComplexSourceReadyLeaf.cost dir sh rows ell p rho visit slots right src dst+
    CompactNativeDenominatorTarget.leafCost n (arity^k)+2*(bits n).length+
    4*(bits (CompactComplexDenominatorPolicy.leafTarget n k)).length+17

/-- Every real descriptor lifecycle, target construction, live commit and
join has a uniform volume-times-visit-count bound from the genuine Path. -/
theorem full_cost_from_path (dir : Direction) (rows ell metadataP : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (slots right src dst R base usedRows n : ℕ)
    (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hpay : sh.payload=1)
    (hP : 2*sh.bits≤metadataP) (hslots : slots≤arity) (hright : right≤sh.active)
    (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    fullCost dir sh rows ell metadataP rho path.visit slots right src dst n≤
      constant*volume rows sh ell metadataP*(arity^k) := by
  have h0 := cost_linear dir rows ell metadataP rho path.visit slots right src dst hr hA hG hpay hP hslots hright hsrc hdst
  have ht := target_native path rows ell metadataP R base usedRows n hr hP hb hu hroom hlive
  have hn := ActiveRepairRankHeadersCommands.bits_length n
  have htarget := ActiveRepairRankHeadersCommands.bits_length (CompactComplexDenominatorPolicy.leafTarget n k)
  have hleaf := CompactComplexControllerDenominatorTarget.leaf_cost_le n (arity^k)
  have hV : 0<volume rows sh ell metadataP := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hN : 0<arity^k := pow_pos (by decide) _
  have hlift := Nat.mul_le_mul_left 100 (Nat.le_mul_of_pos_right (volume rows sh ell metadataP) hN)
  have hden : CompactNativeDenominatorTarget.leafCost n (arity^k)+2*(bits n).length+
      4*(bits (CompactComplexDenominatorPolicy.leafTarget n k)).length+17≤100*volume rows sh ell metadataP := by
    unfold CompactComplexDenominatorPolicy.leafTarget at ht htarget ⊢
    omega
  unfold fullCost constant
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- The complete actual stopped machine carries the uniform proved budget;
all numerical input, raw metadata and live readiness are literal tape facts. -/
theorem runs_linear {s c : ℕ} (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} {levels frames returned : ℕ} (path : Path sh.active left k levels frames returned) (slots right src dst n : ℕ)
    (v : Tapes (CompactComplexSourceReadyStoppedLeaf.publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) slots right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (R base usedRows : ℕ) (hpay : sh.payload=1)
    (hslots : slots≤arity) (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    HoareTime (CompactComplexSourceReadyStoppedLeaf.program dir) (fun z => z=CompactComplexSourceReadyStoppedLeaf.ready v)
      (fun z => z=CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n k))
      (constant*volume rows sh ell p*(arity^k)) := by
  have h := CompactComplexSourceReadyStoppedLeaf.runs dir sh rows ell p rho path.visit slots right src dst n
    v f hG hA hr hp hw hraw hsource hlive htarget
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz)
    (full_cost_from_path dir rows ell p rho path slots right src dst R base usedRows n
      hr hA hG hpay hp hslots hright hsrc hdst hb hu hroom hliveBound)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafBudget
