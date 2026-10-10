import IntegerMultBounds.Machine.CompactComplexNodeLocalBudget
import IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget

/-! Nonleaf return-side cost arithmetic for literal exact contraction, generated
spectator-volume headers, arbitrary-target promotion, live installation, a
second parent codec lifecycle and target/geometry/PC restoration. This pays the
listed component schedules; it does not construct their nonleaf execution or
prove the recursive child's semantic output. Entry/stop/target-save traffic and
recursive child execution are excluded and charged separately. -/
namespace IntegerMultBounds.Machine.CompactComplexChildAlignmentBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open RecursiveChildQuotientsConstant (bits)
open Networks.ComplexRecursiveCallSchema (Call calls)
open ActivePrefixStageParameters (Stage)
attribute [local irreducible] Networks.ComplexRank25.rankSum calls

/-- True before/after dependency ledgers. A completed child's target must be
proved at most its actual live denominator; no completed-network assertion or
cost allowance is embedded in these numerical progress facts. -/
structure Progress (sh : Shape) (metadataP before completed target : ℕ) where
  R : ℕ
  baseline : ℕ
  parentLeft : ℕ
  parentExponent : ℕ
  parentLevels : ℕ
  parentFrames : ℕ
  parentReturned : ℕ
  parentUsed : ℕ
  childLeft : ℕ
  childExponent : ℕ
  childLevels : ℕ
  childFrames : ℕ
  childReturned : ℕ
  childUsed : ℕ
  parentPath : Path sh.active parentLeft parentExponent parentLevels parentFrames parentReturned
  childPath : Path sh.active childLeft childExponent childLevels childFrames childReturned
  metadata : 2*sh.bits≤metadataP
  base : baseline≤metadataP-2*sh.bits
  room : CompactComplexDenominatorCapacity.room R≤sh.chunk
  parentUsed_le : parentUsed≤R
  childUsed_le : childUsed≤R
  before_live : before≤CompactComplexDenominatorCapacity.ledger R baseline
    parentLevels parentFrames parentReturned parentUsed
  completed_live : completed≤CompactComplexDenominatorCapacity.ledger R baseline
    childLevels childFrames childReturned childUsed
  target_growth : target≤before+2*arity^parentExponent
  promote : before≤target
  contract : target≤completed

/-- Literal generated-header promotion and live-commit schedule for the true
chosen target, applicable to either return policy. Three joins are included. -/
def promotionCost (sh : Shape) (c rows ell metadataP : ℕ) (v : Stage sh)
    (selected : Fin c) (before target : ℕ) :=
  ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
    (CompactComplexNativeCodec.raw v rows ell metadataP)+
    (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
      (130*streamVolume sh c rows ell metadataP true+8*target+360)+
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
      (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP
        v.rho v.left v.f v.slots v.right v.source.val v.target.val)+3+
    (2*(bits before).length+4*(bits target).length+15)

def promotionConstant (c : ℕ) := CompactComplexSpectatorVolumeBudget.constant c+498*c+32

/-- The actual denominator capacity pays all spectator scans and target/current
headers, in addition to physically generated length metadata and cleanup. -/
theorem promotion_linear (sh : Shape) (c rows ell metadataP before completed target : ℕ)
    (v : Stage sh) (selected : Fin c) (progress : Progress sh metadataP before completed target)
    (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : CompactSpectatorInheritedGrid.Width sh (rows/c) ell (metadataP-2*sh.bits) f) :
    promotionCost sh c rows ell metadataP v selected before target≤
      promotionConstant c*volume rows sh ell metadataP := by
  have hh := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    v.rho v.left v.f v.slots v.right v.source.val v.target.val true hr hA hG hK
  have hraw : CompactComplexNativeCodec.raw v rows ell metadataP=
      CompactSpectatorLeafSetup.raw sh rows ell metadataP v.rho v.left v.f v.slots v.right v.source.val v.target.val := rfl
  rw [←hraw] at hh
  have hp := CompactComplexDenominatorCapacity.cost_from_path progress.parentPath
    progress.R progress.baseline (metadataP-2*sh.bits) progress.parentUsed before target
    (rows/c) ell (CompactComplexSpectatorPromoteFamily.spectatorList selected).length
    progress.base progress.parentUsed_le progress.room progress.before_live
    progress.target_growth progress.promote hgroup f hw
  dsimp only at hp
  have hv := CompactComplexSpectatorVolumeHeaders.volume_semantic sh c rows ell metadataP true progress.metadata
  simp only [CompactComplexSpectatorVolumeHeaders.roleRows,ite_true] at hv
  rw [CompactComplexStoppedGridHandoff.words_volume sh (rows/c) ell (metadataP-2*sh.bits) f hw,←hv] at hp
  have hs := CompactComplexStoppedAlignedBudget.spectator_count selected
  have hV := CompactComplexControllerExactReturnBudget.stream_le_native sh c rows ell metadataP true
  have hm := Nat.mul_le_mul (show 498*(CompactComplexSpectatorPromoteFamily.spectatorList selected).length+28≤498*c+28 by omega) hV
  have hpos : 0<volume rows sh ell metadataP :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  unfold promotionCost promotionConstant
  nlinarith only [hh,hp,hm,hpos]

/-- Include the genuine second parent codec preparation/cleanup and both joins
around the generated promotion/live-installation lifecycle. -/
def alignmentCost (sh : Shape) (c m d D G K0 ell q rows : ℕ)
    (v : Stage sh) (selected : Fin c) (before target : ℕ) :=
  CompactComplexNativeCodec.prepareCost c m D K0 v.rho ell q d G+
    promotionCost sh c rows ell (CompactNativeRoleReservedBridge.precision c m d D K0 q) v selected before target+
    CompactComplexNativeCodec.cleanupCost ell (CompactNativeRoleReservedBridge.precision c m d D K0 q)+2

def codecConstant (c m : ℕ) := CompactReservationPaddingHeaderBudget.constant c m+5000

/-- Actual target restoration and caller return-PC/header restoration, excluding
child entry and semantic precision return. One connecting join is included. -/
def restoreCost {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (target : ℕ) :=
  CompactComplexCallReturn.addressWidth siteCount arity+3+
    (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot+2*(bits target).length+8)

def restoreConstant (siteCount : ℕ) := CompactComplexNodeLocalBudget.childGeometryConstant siteCount+8

/-- The upper completed-child ledger pays target stack restoration as well as
real return-PC and geometric header traffic. -/
theorem restore_linear {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (rows ell metadataP before completed target : ℕ) (progress : Progress sh metadataP before completed target)
    (hr : 0<rows) (hG : 1≤sh.guard) :
    restoreCost siteCount rho visit ha pair call target≤restoreConstant siteCount*volume rows sh ell metadataP := by
  have hc := CompactComplexControllerChildBudget.lifecycle_linear siteCount rho visit ha pair call.slot
    rows ell metadataP hr hG
  have ht := CompactComplexDenominatorCapacity.target_volume progress.childPath
    progress.R progress.baseline (metadataP-2*sh.bits) progress.childUsed completed target rows ell
    progress.base progress.childUsed_le progress.room progress.completed_live
    (progress.contract.trans (Nat.le_add_right _ _)) hr
  have hv := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell metadataP false progress.metadata
  change streamVolume sh 1 rows ell metadataP false=ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*
    (2*(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2)) at hv
  rw [←hv] at ht
  have htV : target≤volume rows sh ell metadataP := by
    simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
      volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
      CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using ht
  have hl := ActiveRepairRankHeadersCommands.bits_length target
  have hpos : 0<volume rows sh ell metadataP :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  unfold restoreCost restoreConstant
  change _≤CompactComplexNodeLocalBudget.childGeometryConstant siteCount*_ at hc
  nlinarith only [hc,htV,hl,hpos]

/-- All-role exact child contraction remains its own literal schedule, with
its own generated headers, cleanup and live commit. -/
def exactCost (sh : Shape) (c rows ell metadataP : ℕ) (v : Stage sh)
    (completed target : ℕ) :=
  CompactComplexNodeLocalBudget.exactCost sh c rows ell metadataP v.rho v.left v.f v.slots v.right
    v.source.val v.target.val true completed target c

theorem exact_linear (sh : Shape) (c rows ell metadataP before completed target : ℕ)
    (v : Stage sh) (progress : Progress sh metadataP before completed target)
    (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) :
    exactCost sh c rows ell metadataP v completed target≤
      CompactComplexControllerExactReturnBudget.nativeConstant c c*volume rows sh ell metadataP :=
  CompactComplexNodeLocalBudget.exact_linear progress.childPath c rows ell metadataP v.rho v.left v.f
    v.slots v.right v.source.val v.target.val true hgroup hr hG hA hK progress.metadata
    progress.R progress.baseline progress.childUsed completed target c progress.base progress.childUsed_le
    progress.room progress.completed_live progress.contract

/-- One actual return's component context. These fields are literal geometry,
word width and live-progress facts, not supplied runtime allowances. -/
structure Case (sh : Shape) (c ell metadataP : ℕ) where
  parentRows : ℕ
  childRows : ℕ
  parentStage : Stage sh
  childStage : Stage sh
  before : ℕ
  completed : ℕ
  target : ℕ
  progress : Progress sh metadataP before completed target
  selected : Fin c
  rho : Fin sh.chunk
  left : ℕ
  k : ℕ
  visit : Visit sh.active left (k+2)
  active_le : sh.active≤sh.axes
  pair : Networks.BinaryRowProgram.Op (Fin arity)
  parentRows_pos : 0<parentRows
  childRows_pos : 0<childRows
  parentGroup_pos : 0<parentRows/c
  childGroup_pos : 0<childRows/c
  f : CompactSpectatorVisitGeometry.Array sh (parentRows/c) ell
  width : CompactSpectatorInheritedGrid.Width sh (parentRows/c) ell (metadataP-2*sh.bits) f
  nonleaf_target : target=CompactComplexDenominatorPolicy.networkTarget before k

/-- Literal nonleaf return-side component allowance. The child contraction and
parent promotion each have their own generated volume headers and live commit.
Parent codec setup/cleanup, actual target/PC/header restoration, and four joins
between these components are included. No recursive callback cost occurs here. -/
def returnLocalCost (sh : Shape) (c m d D G K0 ell q siteCount : ℕ)
    (call : Call) (ctx : Case sh c ell (CompactNativeRoleReservedBridge.precision c m d D K0 q)) :=
  exactCost sh c ctx.childRows ell (CompactNativeRoleReservedBridge.precision c m d D K0 q)
    ctx.childStage ctx.completed ctx.target+
  alignmentCost sh c m d D G K0 ell q ctx.parentRows ctx.parentStage ctx.selected ctx.before ctx.target+
  restoreCost siteCount ctx.rho ctx.visit ctx.active_le ctx.pair call ctx.target+4

def constant (c m siteCount : ℕ) := codecConstant c m+
  2*(promotionConstant c+CompactComplexControllerExactReturnBudget.nativeConstant c c+
    restoreConstant siteCount)+6

/-- Derive one return allowance from the genuine codec, exact contraction,
spectator promotion, true target/live ledger and restoration schedules. Volume
comparison hypotheses are geometry only, never total cost assumptions. -/
theorem return_local_bound (sh : Shape) (c m d D G K0 ell q siteCount : ℕ)
    (call : Call) (ctx : Case sh c ell (CompactNativeRoleReservedBridge.precision c m d D K0 q))
    (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (hshapeG : 1≤sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (hparent : volume ctx.parentRows sh ell (CompactNativeRoleReservedBridge.precision c m d D K0 q)≤
      2*CompactFallbackAxisRun.volume D K0 ell q)
    (hchild : volume ctx.childRows sh ell (CompactNativeRoleReservedBridge.precision c m d D K0 q)≤
      2*CompactFallbackAxisRun.volume D K0 ell q) :
    returnLocalCost sh c m d D G K0 ell q siteCount call ctx≤
      constant c m siteCount*CompactFallbackAxisRun.volume D K0 ell q := by
  have hcodec := CompactComplexNativeCodec.lifecycle_linear c m D K0 ctx.parentStage.rho ell q d G
    hc hm hd hG hK hD
  have hpromotion := promotion_linear sh c ctx.parentRows ell _ ctx.before ctx.completed ctx.target
    ctx.parentStage ctx.selected ctx.progress ctx.parentRows_pos ctx.parentGroup_pos (by omega) hA hchunk
    ctx.f ctx.width
  have hexact := exact_linear sh c ctx.childRows ell _ ctx.before ctx.completed ctx.target
    ctx.childStage ctx.progress ctx.childRows_pos ctx.childGroup_pos (by omega) hA hchunk
  have hrestore := restore_linear siteCount ctx.rho ctx.visit ctx.active_le ctx.pair call ctx.parentRows ell _
    ctx.before ctx.completed ctx.target ctx.progress ctx.parentRows_pos hshapeG
  have hp := hpromotion.trans (Nat.mul_le_mul_left (promotionConstant c) hparent)
  have he := hexact.trans (Nat.mul_le_mul_left (CompactComplexControllerExactReturnBudget.nativeConstant c c) hchild)
  have hr := hrestore.trans (Nat.mul_le_mul_left (restoreConstant siteCount) hparent)
  have hdim := CompactReservedVolumeBudget.dimension_square_le D K0 ell q
  have hpos : 1≤CompactFallbackAxisRun.volume D K0 ell q := by
    have hsq : 1≤(D*K0+1)^2 := Nat.one_le_pow _ _ (by omega)
    exact hsq.trans hdim
  unfold returnLocalCost alignmentCost constant codecConstant
  nlinarith only [hcodec,hp,he,hr,hpos]

/-- At actual retained descendant row levels, the factor-two comparison with
original unpadded volume is derived, rather than supplied. -/
theorem actual_return_local_bound (c m d D G K0 ell q siteCount parentLevel childLevel : ℕ)
    (call : Call)
    (ctx : Case (CompactReservationNativeRows.shape c m d D G K0) c ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q))
    (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (hshapeG : 1≤(CompactReservationNativeRows.shape c m d D G K0).guard)
    (hA : 0<(CompactReservationNativeRows.shape c m d D G K0).axes)
    (hchunk : 0<(CompactReservationNativeRows.shape c m d D G K0).chunk)
    (hparent : ctx.parentRows=CompactGlobalRowPadding.rowsAt c m d K0 parentLevel)
    (hchild : ctx.childRows=CompactGlobalRowPadding.rowsAt c m d K0 childLevel) :
    returnLocalCost _ c m d D G K0 ell q siteCount call ctx≤
      constant c m siteCount*CompactFallbackAxisRun.volume D K0 ell q := by
  apply return_local_bound _ c m d D G K0 ell q siteCount call ctx hc hm hd hG hK hD hshapeG hA hchunk
  · rw [hparent]
    exact CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q parentLevel (by omega) hK hD
  · rw [hchild]
    exact CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q childLevel (by omega) hK hD

private theorem list_sum_bound {α : Type*} (xs : List α) (f : α → ℕ) (A : ℕ)
    (hf : ∀ x ∈ xs,f x≤A) : (xs.map f).sum≤xs.length*A := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      f x+(xs.map f).sum≤A+xs.length*A := Nat.add_le_add hx ht
      _ = _ := by ring

/-- Actual literal call multiplicity, with independently changing dependency
Paths and true denominators in each context. Callback runtimes remain exactly
their separate original-occurrence sum. This is schedule-cost arithmetic, not
an asserted assembled nonleaf machine execution. -/
theorem actual_return_sum (c m d D G K0 ell q siteCount : ℕ)
    (ctx : Call → Case (CompactReservationNativeRows.shape c m d D G K0) c ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q))
    (parentLevel childLevel callbackCost : Call → ℕ)
    (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (hshapeG : 1≤(CompactReservationNativeRows.shape c m d D G K0).guard)
    (hA : 0<(CompactReservationNativeRows.shape c m d D G K0).axes)
    (hchunk : 0<(CompactReservationNativeRows.shape c m d D G K0).chunk)
    (hparent : ∀ call,(ctx call).parentRows=CompactGlobalRowPadding.rowsAt c m d K0 (parentLevel call))
    (hchild : ∀ call,(ctx call).childRows=CompactGlobalRowPadding.rowsAt c m d K0 (childLevel call)) :
    (calls.map (fun call => returnLocalCost _ c m d D G K0 ell q siteCount call (ctx call))).sum+
      (calls.map callbackCost).sum≤
      (Networks.ComplexRank25.rankSum*constant c m siteCount)*CompactFallbackAxisRun.volume D K0 ell q+
        (calls.map callbackCost).sum := by
  have hs := list_sum_bound calls _ (constant c m siteCount*CompactFallbackAxisRun.volume D K0 ell q)
    (fun call _ => actual_return_local_bound c m d D G K0 ell q siteCount (parentLevel call) (childLevel call)
      call (ctx call) hc hm hd hG hK hD hshapeG hA hchunk (hparent call) (hchild call))
  rw [Networks.ComplexRecursiveCallSchema.calls_rankSum] at hs
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right hs ((calls.map callbackCost).sum)

end
end IntegerMultBounds.Machine.CompactComplexChildAlignmentBudget
