import IntegerMultBounds.Machine.CompactNativeRoleChildLifecycleBudget

/-! The complete actual stopped child caller pays all native metadata from
the original serialized word. No decoder normalization follows from this cost
or from matching the unchanged signed field width. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleStoppedChildBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafSetup (raw)
open CompactSpectatorLeafGuardOriginal (Direction)
open RecursiveChildQuotientsConstant (bits)

theorem baseline_reservation (s : Shape) (p : ℕ) (hp : 2*s.bits≤p) :
    ButterflyIndependentGuardHeaders.reservation s.bits (p-2*s.bits)=p := by
  unfold ButterflyIndependentGuardHeaders.reservation
  omega

theorem guard_payload (s : Shape) (ell p : ℕ) (hp : 2*s.bits≤p) :
    (NativePolynomialStageShape.shape s ell p).payload=
      3*(2^ell*ButterflyAxisHeadersData.recordLength (NativePolynomialStageShape.shape s ell p).bits
        (ButterflyIndependentGuardHeaders.reservation (NativePolynomialStageShape.shape s ell p).bits (p-2*s.bits))) := by
  rw [NativePolynomialStageShape.bits,baseline_reservation s p hp]
  unfold NativePolynomialStageShape.shape NativePolynomialStageShape.payload NativePolynomialStageShape.width
    ActivePrefixStageNativePolynomial.symbols ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    ButterflyGuard.width ButterflyGuard.halfWidth
  ring

theorem guard_volume (s : Shape) (rows ell p : ℕ) (hp : 2*s.bits≤p) :
    CompactSpectatorLeafGuardBudget.volume (NativePolynomialStageShape.shape s ell p) rows ell (p-2*s.bits)=
      volume rows s ell p := by
  unfold CompactSpectatorLeafGuardBudget.volume CompactSpectatorLeafAxisBudget.volume
  rw [NativePolynomialStageShape.bits,baseline_reservation s p hp]
  unfold ButterflySpectatorBudget.volume ButterflyAxisHeadersBudget.logicalVolume ButterflyAxisHeadersData.recordLength
    ButterflyAxisHeadersData.width volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
  ring

theorem node_scalar (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) :
    CompactSpectatorLeafSetupBudget.scalar s rows ell p rho.val left (arity^(k+1)) arity
      (node rho visit hactive).right pair.source.val pair.target.val≤19*volume rows s ell p := by
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := NativePolynomialStageHeaderBudget.scalar_le
    (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rows ell p hr hA hG hK hpay
  change CompactSpectatorLeafSetupBudget.scalar s rows ell p rho.val left (arity^k) arity
    (node rho visit hactive).right pair.source.val pair.target.val≤18*volume rows s ell p at h0
  have hbits := (CompactNativeRoleHeaderBudget.values_le s rows ell p hr).1
  have ha : s.active≤s.bits := by
    have hm := Nat.le_mul_of_pos_right s.active hK
    unfold Shape.bits
    omega
  have hf := visit.fits
  unfold CompactSpectatorLeafSetupBudget.scalar at h0 ⊢
  omega

theorem expanded_scalar (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) :
    CompactSpectatorLeafSetupBudget.scalar (NativePolynomialStageShape.shape s ell p) rows ell p rho.val left
      (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val≤22*volume rows s ell p := by
  have h0 := node_scalar s rows ell p rho visit hactive pair hr hG hA hpay
  have h1 := NativePolynomialStageHeaderBudget.payload_le s rows ell p hr
  have he : CompactSpectatorLeafSetupBudget.scalar (NativePolynomialStageShape.shape s ell p) rows ell p rho.val left
      (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val+s.payload=
    CompactSpectatorLeafSetupBudget.scalar s rows ell p rho.val left (arity^(k+1)) arity
      (node rho visit hactive).right pair.source.val pair.target.val+NativePolynomialStageShape.payload s ell p := by
    dsimp [CompactSpectatorLeafSetupBudget.scalar,NativePolynomialStageShape.shape,Shape.bits,Shape.H,Shape.B,Shape.F]
    ring
  omega

theorem payload_lifecycle (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) :
    NativePolynomialStageHeaders.cost s rows ell p rho.val left (arity^(k+1)) arity
      (node rho visit hactive).right pair.source.val pair.target.val+
    ButterflyAxisHeadersArithmetic.scheduleCost NativePolynomialStageHeaders.restore
      (NativePolynomialStageHeaders.prepared s rows ell p rho.val left (arity^(k+1)) arity
        (node rho visit hactive).right pair.source.val pair.target.val)≤
          NativePolynomialStageHeaderBudget.constant*volume rows s ell p := by
  have hK : 0<s.chunk := by have := rho.isLt; omega
  rw [CompactNativeRoleChildLifecycleBudget.payload_count_irrelevant s rows ell p rho.val left
    (arity^(k+1)) (arity^k) arity (node rho visit hactive).right pair.source.val pair.target.val (Nat.mul_pos hA hG) hK]
  exact NativePolynomialStageHeaderBudget.lifecycle_linear
    (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rows ell p hr hA hG hK hpay

theorem precision_lifecycle (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) :
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.prepare
      (raw (NativePolynomialStageShape.shape s ell p) rows ell p rho.val left (arity^(k+1)) arity
        (node rho visit hactive).right pair.source.val pair.target.val)+
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.restore
      (CompactNativeRoleChildPrecision.baseline (NativePolynomialStageShape.shape s ell p) rows ell p rho.val left
        (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val)≤
          1110000*volume rows s ell p := by
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := CompactNativeRoleChildLifecycleBudget.precision_rest_cost (NativePolynomialStageShape.shape s ell p)
    rows ell p rho.val left (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val (Nat.mul_pos hA hG) hK
  have h1 := CompactSpectatorLeafSetupBudget.geometry_cost (NativePolynomialStageShape.shape s ell p)
    rows ell p rho.val left (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val (Nat.mul_pos hA hG) hK
  have h2 := expanded_scalar s rows ell p rho visit hactive pair hr hG hA hpay
  have h3 := CompactNativeRoleHeaderBudget.values_le s rows ell p hr
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  simp only [NativePolynomialStageShape.bits] at h0
  omega

def guardedConstant (c : ℕ) := 12000*(c+1)+NativePolynomialStageHeaderBudget.constant+
  1110000+CompactSpectatorLeafGuardBudget.phaseConstant+6

theorem guarded_linear (dir : Direction) (c : ℕ) (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (hc : 0<c) (hr : 0<rows) (hd : c∣rows)
    (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) (hp : 2*s.bits≤p) :
    CompactNativeRoleGuardedChildCaller.cost dir c s rows ell p rho visit arity
      (node rho visit hactive).right pair.source.val pair.target.val≤
        guardedConstant c*volume rows s ell p*(arity^(k+1)) := by
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have h0 := CompactNativeRoleChildLifecycleBudget.row_cost c s rows ell p rho.val left (arity^(k+1)) arity
    (node rho visit hactive).right pair.source.val pair.target.val hr hd
  have h1 := payload_lifecycle s (rows/c) ell p rho visit hactive pair hn hG hA hpay
  have h2 := precision_lifecycle s (rows/c) ell p rho visit hactive pair hn hG hA hpay
  have hright : (node rho visit hactive).right≤s.active := by have := (node rho visit hactive).activeAxes; omega
  have h3 := CompactSpectatorLeafGuardBudget.phase_cost dir (NativePolynomialStageShape.shape s ell p)
    (rows/c) ell (p-2*s.bits) rho visit arity (node rho visit hactive).right pair.source.val pair.target.val
    hG hA hn le_rfl hright (Nat.le_of_lt pair.source.isLt) (Nat.le_of_lt pair.target.isLt) (guard_payload s ell p hp)
  rw [guard_volume s (rows/c) ell p hp] at h3
  have hchild : volume (rows/c) s ell p≤volume rows s ell p :=
    Nat.mul_le_mul_right _ (Nat.div_le_self rows c)
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hVN := Nat.le_mul_of_pos_right (volume rows s ell p) hN
  have hl0 := Nat.mul_le_mul_left (10000*(c+1)+2000*(c+1)) hVN
  have hl1 := Nat.mul_le_mul_left NativePolynomialStageHeaderBudget.constant (hchild.trans hVN)
  have hl2 := Nat.mul_le_mul_left 1110000 (hchild.trans hVN)
  have hl3 := Nat.mul_le_mul_right (arity^(k+1))
    (Nat.mul_le_mul_left CompactSpectatorLeafGuardBudget.phaseConstant hchild)
  unfold CompactNativeRoleGuardedChildCaller.cost guardedConstant
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.mul_add] at *
  omega

theorem count_lifecycle (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :
    CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.expand
      (CompactNativeRoleStoppedChildCaller.nodeState s rows ell p rho visit hactive pair)+
    CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.restore
      (CompactSpectatorLeafCountBudget.expanded
        (CompactNativeRoleStoppedChildCaller.nodeState s rows ell p rho visit hactive pair) arity (arity^k))≤
      (10000*(arity+1)+2000)*(arity^(k+1)) := by
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hf : arity^k≤arity^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have ha : arity≤arity^(k+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left arity (pow_pos (by decide) k)
  have hq := CompactNativeRoleHeaderBudget.quotient_linear (arity^k*arity) arity
    (Nat.mul_pos (pow_pos (by decide) k) (by decide))
  have he := CompactSpectatorLeafCountBudget.expand_cost
    (CompactNativeRoleStoppedChildCaller.nodeState s rows ell p rho visit hactive pair) arity (arity^k) rfl rfl
  have hdiv : arity^k*arity/arity=arity^k := Nat.mul_div_cancel _ (by decide)
  simp [CompactSpectatorLeafCountBudget.restore,CompactChildHeadersArithmetic.scheduleCost,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,CompactSpectatorLeafCountBudget.expanded,
    CompactNativeRoleStoppedChildCaller.nodeState,raw,Function.update,hdiv] at ⊢
  dsimp only [CompactNativeRoleStoppedChildCaller.nodeState] at he
  simp only [←pow_succ,Nat.add_mul] at he hq ⊢
  omega

def constant (c : ℕ) := guardedConstant c+10000*(arity+1)+2002

theorem cost_linear (dir : Direction) (c : ℕ) (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (hc : 0<c) (hr : 0<rows) (hd : c∣rows)
    (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) (hp : 2*s.bits≤p) :
    CompactNativeRoleStoppedChildCaller.cost dir c s rows ell p rho visit hactive pair≤
      constant c*volume rows s ell p*(arity^(k+1)) := by
  have h0 := guarded_linear dir c s rows ell p rho visit hactive pair hc hr hd hG hA hpay hp
  have h1 := count_lifecycle s rows ell p rho visit hactive pair
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hscale := Nat.mul_le_mul_right (arity^(k+1))
    (Nat.le_mul_of_pos_right (10000*(arity+1)+2000) hV)
  have hVN : 0<volume rows s ell p*(arity^(k+1)) := Nat.mul_pos hV hN
  unfold CompactNativeRoleStoppedChildCaller.cost constant
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

theorem actual_active (c m d D G K : ℕ) (hDd : D≤d) :
    (CompactReservationNativeRows.shape c m d D G K).active≤(CompactReservationNativeRows.shape c m d D G K).axes := by
  change D-CompactGlobalReservation.reservedAxes c m d G K≤d
  omega

/-- Actual descendant geometry pays the entire stopped role caller from the
original unpadded native symbol volume, including its generated codec payload. -/
theorem actual_cost_linear (dir : Direction) (c m d D G K ell q j : ℕ)
    (hDd : D≤d) (hc : 0<c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hj : j<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape c m d D G K).chunk) {left k : ℕ}
    (visit : Visit (CompactReservationNativeRows.shape c m d D G K).active left (k+1))
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :
    CompactNativeRoleStoppedChildCaller.cost dir c (CompactReservationNativeRows.shape c m d D G K)
      (CompactGlobalRowPadding.rowsAt c m d K j) ell (CompactNativeRoleReservedBridge.precision c m d D K q)
      rho visit (actual_active c m d D G K hDd) pair≤
        (2*constant c)*CompactFallbackAxisRun.volume D K ell q*(arity^(k+1)) := by
  have hr := CompactGlobalRowPadding.rowsAt_positive c m d K j hc hK (by omega)
  have hdiv := CompactGlobalRowPadding.split_divides c m d K j hc hK hj
  have h0 := cost_linear dir c (CompactReservationNativeRows.shape c m d D G K)
    (CompactGlobalRowPadding.rowsAt c m d K j) ell (CompactNativeRoleReservedBridge.precision c m d D K q)
    rho visit (actual_active c m d D G K hDd) pair hc hr hdiv hG hd rfl
    (CompactNativeRoleChildPrecision.actual_precision c m d D G K q hK hD).1
  have hrow := CompactGlobalRowPadding.rowsAt_le_initial c m d K j
  have hvol := Nat.mul_le_mul_right
    (CompactNativeRoleOriginal.symbols (CompactReservationNativeRows.shape c m d D G K) ell
      (CompactNativeRoleReservedBridge.precision c m d D K q)) hrow
  have hpad := CompactNativeRoleTransferBudget.reservation_volume c m d D G K ell q hc hK hD
  have h1 := Nat.mul_le_mul_right (arity^(k+1)) (Nat.mul_le_mul_left (constant c) (hvol.trans hpad))
  convert h0.trans h1 using 1
  ring

/-- Full shape width/hrecord premises are derived from the actual corrected
precision and generated row codec. This statement makes no grid assertion. -/
theorem actual_codec (c m d D G K ell q : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    let s := CompactReservationNativeRows.shape c m d D G K
    let p := CompactNativeRoleReservedBridge.precision c m d D K q
    (NativePolynomialStageShape.shape s ell p).payload=
      ActivePrefixStageNativePolynomial.symbols (2^ell) (ButterflyGuard.width p s.bits)*3 ∧
    s.bits+1≤(NativePolynomialStageShape.shape s ell p).payload ∧
    CompactNativeRoleHeaders.recordWidth s p=
      ButterflyAxisHeadersData.width s.bits
        (ButterflyIndependentGuardHeaders.reservation s.bits (p-2*s.bits)) := by
  dsimp only
  exact ⟨rfl,NativePolynomialStageShape.payload_fits _ _ _,
    CompactNativeRoleChildPrecision.stored_width _ _ (CompactNativeRoleChildPrecision.actual_precision c m d D G K q hK hD).1⟩

end
end IntegerMultBounds.Machine.CompactNativeRoleStoppedChildBudget
