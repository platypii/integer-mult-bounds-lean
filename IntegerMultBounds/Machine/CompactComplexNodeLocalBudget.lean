import IntegerMultBounds.Machine.CompactComplexScalarGroupProgress
import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
import IntegerMultBounds.Machine.CompactComplexControllerChildBudget
import IntegerMultBounds.Machine.CompactComplexRootPieceVolume
import IntegerMultBounds.Machine.CompactComplexRecursiveRuntimeSum

/-! Actual scalar group, geometric descriptor/return-PC and exact-return metadata costs
are linear in native volume with fixed compiler constants. Recursive callback
runtimes remain their literal separate sum. These partial local expressions do not include per-child spectator alignment,
codec lifecycles or every sequencing join. Full recursive assembly is separate. -/
namespace IntegerMultBounds.Machine.CompactComplexNodeLocalBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexScalarIntegerRows (GroupIndex RowIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCountLifecycle (cost timeConstant)
open CompactNativeRoleTransferBudget (volume)
open Networks.ComplexRecursiveCallSchema (Call calls)
attribute [local irreducible] Networks.ComplexRank25.program
  CompactComplexScalarIntegerRows.gates Networks.ComplexRecursiveCallSchema.calls
  Networks.ComplexRank25.rankSum

/-- Sum the actual fixed named group constants, without evaluating the enormous
closed network during elaboration. -/
@[irreducible] def scalarConstant : ℕ := ∑ g : GroupIndex,timeConstant (block g)

private theorem scalar_constant_eq : scalarConstant =
    ∑ g : GroupIndex,timeConstant (block g) := by unfold scalarConstant; rfl

/-- Literal costs include original count setup, all scalar rows, physical
live increments, count erasure and both joins for every original group. -/
def scalarCost (sh : Shape) (rows ell metadataP : ℕ) (live : GroupIndex → ℕ) :=
  ∑ g : GroupIndex,cost (block g) (rows*2^sh.bits*2^ell)
    (ButterflyGuard.halfWidth metadataP sh.bits+1) (live g)

private theorem scalar_measure (sh : Shape) (rows ell metadataP : ℕ) :
    rows*2^sh.bits*2^ell*(ButterflyGuard.halfWidth metadataP sh.bits+2)≤
      volume rows sh ell metadataP := by
  unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    CompactNativeRoleHeaders.recordWidth ButterflyGuard.width
  have he : rows*(2^sh.bits*2^ell*(2*(ButterflyGuard.halfWidth metadataP sh.bits+1+1))) =
      2*(rows*2^sh.bits*2^ell*(ButterflyGuard.halfWidth metadataP sh.bits+2)) := by ring
  rw [he]
  omega

/-- A complete original scalar network has one fixed linear-volume allowance;
no desired aggregate allowance is supplied. -/
theorem scalar_linear (sh : Shape) (rows ell metadataP : ℕ) (live : GroupIndex → ℕ)
    (hr : 0<rows)
    (hlive : ∀ g,live g≤ButterflyGuard.halfWidth metadataP sh.bits+1) :
    scalarCost sh rows ell metadataP live≤scalarConstant*volume rows sh ell metadataP := by
  have hn : 1≤rows*2^sh.bits*2^ell := by
    have hpos : 0<rows*2^sh.bits*2^ell := by positivity
    omega
  have hs : scalarCost sh rows ell metadataP live≤
      (∑ g : GroupIndex,timeConstant (block g))*
        (rows*2^sh.bits*2^ell*(ButterflyGuard.halfWidth metadataP sh.bits+2)) := by
    unfold scalarCost
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro g _
    have h := CompactComplexScalarCountLifecycle.cost_linear (block g)
      (rows*2^sh.bits*2^ell) (ButterflyGuard.halfWidth metadataP sh.bits+1)
      (live g) hn (hlive g)
    simpa only [Nat.add_assoc,Nat.mul_assoc] using h
  rw [←scalar_constant_eq] at hs
  exact hs.trans (Nat.mul_le_mul_left _ (scalar_measure sh rows ell metadataP))

/-- The actual Path and scalar-prefix progress discharge every group capacity.
The denominator is the true physical value, not an independent cost parameter. -/
theorem scalar_linear_from_path {sh : Shape} {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (rows ell metadataP baseline : ℕ) (live : GroupIndex → ℕ) (hr : 0<rows) (hp : 2*sh.bits≤metadataP)
    (hb : baseline≤metadataP-2*sh.bits)
    (hroom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
    (hlive : ∀ g,live g≤CompactComplexDenominatorCapacity.ledger
      CompactComplexDenominatorCapacity.scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows g.val).length) :
    scalarCost sh rows ell metadataP live≤scalarConstant*volume rows sh ell metadataP := by
  apply scalar_linear sh rows ell metadataP live hr
  intro g
  have hcap := CompactComplexControllerExactReturnBudget.current_capacity path
    CompactComplexDenominatorCapacity.scalarRows baseline (metadataP-2*sh.bits)
    (CompactFramedScalarGrid.rows g.val).length (live g) hb
    (CompactComplexDenominatorCapacity.actual_prefix g.val) hroom (hlive g)
  unfold CompactSpectatorInheritedGrid.half at hcap
  unfold ButterflyGuard.halfWidth at hcap ⊢
  omega


/-- Interleaved child returns may change the dependency Path between scalar
groups. Each actual group uses its own true progress ledger; no common
returned-count or inherited capacity is silently assumed. -/
theorem scalar_linear_from_paths (sh : Shape)
    (left exponent levels frames returned : GroupIndex → ℕ)
    (paths : ∀ g,CompactRecursiveDependencyBudget.Path sh.active (left g) (exponent g)
      (levels g) (frames g) (returned g))
    (rows ell metadataP baseline : ℕ) (live : GroupIndex → ℕ)
    (hr : 0<rows) (hp : 2*sh.bits≤metadataP)
    (hb : baseline≤metadataP-2*sh.bits)
    (hroom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
    (hlive : ∀ g,live g≤CompactComplexDenominatorCapacity.ledger
      CompactComplexDenominatorCapacity.scalarRows baseline (levels g) (frames g) (returned g)
      (CompactFramedScalarGrid.rows g.val).length) :
    scalarCost sh rows ell metadataP live≤scalarConstant*volume rows sh ell metadataP := by
  apply scalar_linear sh rows ell metadataP live hr
  intro g
  have hcap := CompactComplexControllerExactReturnBudget.current_capacity (paths g)
    CompactComplexDenominatorCapacity.scalarRows baseline (metadataP-2*sh.bits)
    (CompactFramedScalarGrid.rows g.val).length (live g) hb
    (CompactComplexDenominatorCapacity.actual_prefix g.val) hroom (hlive g)
  unfold CompactSpectatorInheritedGrid.half at hcap
  unfold ButterflyGuard.halfWidth at hcap ⊢
  omega

/-- Compile-time child controller constant, symbolic in the actual site count. -/
def childGeometryConstant (siteCount : ℕ) :=
  4*(CompactComplexChildHeadersUniform.constant+
    2*CompactComplexCallReturn.addressWidth siteCount arity+212)

/-- Geometric child headers and return-PC traffic only. Target selection,
denominator save/restore, spectator alignment and commit are absent here. -/
def childGeometryCost {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Call → Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ) :=
  (calls.map (fun call =>
    CompactComplexControllerChildBudget.entryCost siteCount rho visit ha (pair call) call.slot rows+
      CompactComplexCallReturn.addressWidth siteCount arity+5+
      CompactComplexControllerChildBudget.returnCost rho visit ha (pair call) call.slot+2)).sum

private theorem list_cost_le {α : Type*} (xs : List α) (f : α → ℕ) (A : ℕ)
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

/-- Original repeated geometric-header/PC occurrences are all paid once.
This is not the full child controller: target selection and stack traffic
are accounted by the separate target-controller lemmas below. -/
theorem child_geometry_linear {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Call → Networks.BinaryRowProgram.Op (Fin arity)) (rows ell metadataP : ℕ)
    (hr : 0<rows) (hG : 1≤sh.guard) :
    childGeometryCost siteCount rho visit ha pair rows≤
      (Networks.ComplexRank25.rankSum*childGeometryConstant siteCount)*volume rows sh ell metadataP := by
  have h := list_cost_le calls _ (childGeometryConstant siteCount*volume rows sh ell metadataP)
    (fun call _ => CompactComplexControllerChildBudget.lifecycle_linear siteCount rho visit ha
      (pair call) call.slot rows ell metadataP hr hG)
  simpa only [childGeometryCost,Networks.ComplexRecursiveCallSchema.calls_rankSum,Nat.mul_assoc] using h


/-- The literal target controller: real stop computation and target selection,
save/clear of the target before entry, geometric entry, return-PC pop,
parent-header return, target-stack restore and the three sequencing joins.
Spectator alignment and live commit occur separately after this expression. -/
def childTargetCost {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows n : ℕ) :=
  let targetN := CompactComplexControllerChildStopTarget.chosenTarget sh.axes (k+1) n (arity^(k+1))
  CompactComplexControllerChildStopTarget.cost sh.axes (k+2) n (arity^(k+1))+
    (4*(RecursiveChildQuotientsConstant.bits targetN).length+13+
      CompactComplexControllerChildBudget.entryCost siteCount rho visit ha pair call.slot rows)+
    (CompactComplexCallReturn.addressWidth siteCount arity+3+
      (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot+
        2*(RecursiveChildQuotientsConstant.bits targetN).length+8))+3

/-- This constant includes actual runtime stop/target selection and target
save/restore as well as the geometric-header and real return-PC traffic. -/
def targetControllerConstant (siteCount : ℕ) := childGeometryConstant siteCount+
  11*CompactComplexControllerChildStopTarget.timeConstant+32

private theorem target_control_arithmetic (stop entry ret addr len V A T : ℕ)
    (hs : stop≤T*(11*V)) (hc : entry+addr+5+ret+2≤A*V)
    (hl : len≤2*V) (hV : 0<V) :
    stop+(4*len+13+entry)+(addr+3+(ret+2*len+8))+3≤(A+11*T+32)*V := by
  nlinarith

/-- All literal target-selection and target-stack costs are linear in native
volume. The numerical premise is discharged from the real Path below. -/
theorem child_target_linear {sh : Shape} {left k : ℕ} (siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows ell metadataP n : ℕ)
    (hr : 0<rows) (hG : 1≤sh.guard)
    (hn : n+2*arity^(k+1)≤volume rows sh ell metadataP) :
    childTargetCost siteCount rho visit ha pair call rows n≤
      targetControllerConstant siteCount*volume rows sh ell metadataP := by
  let V := volume rows sh ell metadataP
  have hV : 0<V := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hd := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=sh) rows ell metadataP hr hG
  have hsquare : sh.axes+1≤(sh.axes+1)^2 := by nlinarith only []
  have he := CompactComplexControllerChildBudget.exponent_bound visit ha
  have harg : sh.axes+(k+2)+n+arity^(k+1)+1≤11*V := by
    have hdim : sh.axes+1≤4*V := hsquare.trans hd
    change n+2*arity^(k+1)≤V at hn
    omega
  have hstop := (CompactComplexControllerChildStopTarget.cost_le sh.axes (k+2) n (arity^(k+1))).trans
    (Nat.mul_le_mul_left CompactComplexControllerChildStopTarget.timeConstant harg)
  have htarget : CompactComplexControllerChildStopTarget.chosenTarget sh.axes (k+1) n (arity^(k+1))≤V := by
    unfold CompactComplexControllerChildStopTarget.chosenTarget
    split_ifs <;> omega
  have hlen := ActiveRepairRankHeadersCommands.bits_length
    (CompactComplexControllerChildStopTarget.chosenTarget sh.axes (k+1) n (arity^(k+1)))
  have hbits : (RecursiveChildQuotientsConstant.bits
      (CompactComplexControllerChildStopTarget.chosenTarget sh.axes (k+1) n (arity^(k+1)))).length≤2*V := by
    omega
  have hgeometry := CompactComplexControllerChildBudget.lifecycle_linear siteCount rho visit ha pair call.slot
    rows ell metadataP hr hG
  exact target_control_arithmetic _ _ _ _ _ V (childGeometryConstant siteCount)
    CompactComplexControllerChildStopTarget.timeConstant hstop hgeometry hbits hV

/-- The true live ledger pays the maximum of both actual return policies from
original retained geometry, removing an independent target-cost allowance. -/
theorem child_target_linear_from_path {sh : Shape} {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (siteCount : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (rows ell metadataP R baseline usedRows n : ℕ)
    (hr : 0<rows) (hG : 1≤sh.guard) (hp : 2*sh.bits≤metadataP)
    (hb : baseline≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows) :
    childTargetCost siteCount rho visit ha pair call rows n≤
      targetControllerConstant siteCount*volume rows sh ell metadataP := by
  have hpow : arity^(k+1)≤arity^(k+2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have htarget := CompactComplexDenominatorCapacity.target_volume path R baseline (metadataP-2*sh.bits)
    usedRows n (n+2*arity^(k+1)) rows ell hb hu hroom hlive
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpow) n) hr
  have hv := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell metadataP false hp
  change CompactComplexSpectatorVolumeHeaders.streamVolume sh 1 rows ell metadataP false =
    ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*
      (2*(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2)) at hv
  rw [←hv] at htarget
  have hn : n+2*arity^(k+1)≤volume rows sh ell metadataP := by
    simpa only [CompactComplexSpectatorVolumeHeaders.streamVolume,
      CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,volume,
      CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
      CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using htarget
  exact child_target_linear siteCount rho visit ha pair call rows ell metadataP n hr hG hn

/-- Repeated actual target-controller costs keep the true child callback sum
separate. Each occurrence uses its own dependency Path and physical live value. -/
theorem child_targets_sum_from_paths (sh : Shape) (left : ℕ) (k siteCount : ℕ)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Call → Networks.BinaryRowProgram.Op (Fin arity))
    (levels frames returned usedRows live : Call → ℕ)
    (paths : ∀ call,CompactRecursiveDependencyBudget.Path sh.active left (k+2)
      (levels call) (frames call) (returned call))
    (rows ell metadataP R baseline : ℕ)
    (hr : 0<rows) (hG : 1≤sh.guard) (hp : 2*sh.bits≤metadataP)
    (hb : baseline≤metadataP-2*sh.bits) (hu : ∀ call,usedRows call≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : ∀ call,live call≤CompactComplexDenominatorCapacity.ledger R baseline
      (levels call) (frames call) (returned call) (usedRows call)) :
    (calls.map (fun call => childTargetCost siteCount rho visit ha (pair call) call rows (live call))).sum≤
      (Networks.ComplexRank25.rankSum*targetControllerConstant siteCount)*volume rows sh ell metadataP := by
  have h := list_cost_le calls _ (targetControllerConstant siteCount*volume rows sh ell metadataP)
    (fun call _ => child_target_linear_from_path (paths call) siteCount rho visit ha (pair call) call
      rows ell metadataP R baseline (usedRows call) (live call) hr hG hp hb (hu call) hroom (hlive call))
  simpa only [Networks.ComplexRecursiveCallSchema.calls_rankSum,Nat.mul_assoc] using h

/-- The literal exact-return schedule, including generated volume metadata,
all-role contraction, cleanup, commit and joins. -/
def exactCost (sh : Shape) (headerCount rows ell metadataP rho left count slots right src dst : ℕ)
    (merge : Bool) (current target c : ℕ) :=
  let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
  ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
    c*(129*CompactComplexSpectatorVolumeHeaders.streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+
    (2*(RecursiveChildQuotientsConstant.bits current).length+
      4*(RecursiveChildQuotientsConstant.bits target).length+15)+3

/-- All numerical/header allowances of the actual completed return are paid
from native volume, using genuine live progress and retained capacity. -/
theorem exact_linear {sh : Shape} {pathLeft k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active pathLeft k levels frames returned)
    (headerCount rows ell metadataP rho left count slots right src dst : ℕ) (merge : Bool)
    (hgroup : 0<rows/headerCount) (hr : 0<rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hp : 2*sh.bits≤metadataP)
    (R baseline usedRows current target c : ℕ)
    (hb : baseline≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows)
    (ht : target≤current) :
    exactCost sh headerCount rows ell metadataP rho left count slots right src dst merge current target c≤
      CompactComplexControllerExactReturnBudget.nativeConstant headerCount c*volume rows sh ell metadataP :=
  CompactComplexControllerExactReturnBudget.raw_cost_native path
    headerCount rows ell metadataP rho left count slots right src dst merge hgroup hr hG hA hK hp
    R baseline usedRows current target c hb hu hroom hlive ht

/-- Scalar, fixed child control and completed return coefficients depend only
on the original network and fixed compiler parameters. -/
def partialConstant (siteCount headerCount c : ℕ) := scalarConstant+
  Networks.ComplexRank25.rankSum*childGeometryConstant siteCount+
  CompactComplexControllerExactReturnBudget.nativeConstant headerCount c

/-- These partial linear components are absorbed at the interchange exponent. The
physical interchange bound is an honest separate component premise; no total
local or complete recursive runtime allowance is assumed. -/
theorem absorb_partial_local (scalar control exact interchange V width siteCount headerCount c : ℕ)
    {I : ℝ} (hwidth : 1≤width)
    (hs : scalar≤scalarConstant*V)
    (hc : control≤(Networks.ComplexRank25.rankSum*childGeometryConstant siteCount)*V)
    (he : exact≤CompactComplexControllerExactReturnBudget.nativeConstant headerCount c*V)
    (hi : (interchange : ℝ)≤I*(V : ℝ)*(width : ℝ)^Parameters.tau) :
    ((scalar+control+exact+interchange : ℕ) : ℝ)≤
      ((partialConstant siteCount headerCount c : ℕ)+I)*(V : ℝ)*(width : ℝ)^Parameters.tau := by
  have hsum : scalar+control+exact≤partialConstant siteCount headerCount c*V := by
    unfold partialConstant
    nlinarith only [hs,hc,he]
  have hsumR : ((scalar+control+exact : ℕ) : ℝ)≤
      (partialConstant siteCount headerCount c : ℝ)*V := by exact_mod_cast hsum
  have hw : (1 : ℝ)≤(width : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast hwidth)
      CompactComplexRecursiveRuntimeSum.exponents.1.le
  have hscaled := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (Nat.cast_nonneg (partialConstant siteCount headerCount c)) (Nat.cast_nonneg V))
  push_cast at hsumR ⊢
  nlinarith only [hsumR,hi,hscaled]


/-- A genuine row split gives the original role-volume quotient exactly. This
requires actual row divisibility; it is not inferred from a field width. -/
theorem role_quotient (sh : Shape) (rows ell metadataP c : ℕ)
    (hc : 0<c) (hrows : c∣rows) :
    volume (rows/c) sh ell metadataP=volume rows sh ell metadataP/c := by
  obtain ⟨n,rfl⟩ := hrows
  simp only [volume,Nat.mul_div_cancel_left _ hc]
  rw [Nat.mul_assoc,Nat.mul_div_cancel_left _ hc]

/-- Uniform scalar and child-control costs are paid by original unpadded
geometry even at descendants, with the actual factor-two row padding. -/
theorem original_volume (c m d D G K0 ell q level : ℕ) (hc : 0<c) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D) :
    volume (CompactGlobalRowPadding.rowsAt c m d K0 level)
      (CompactReservationNativeRows.shape c m d D G K0) ell
      (CompactNativeRoleReservedBridge.precision c m d D K0 q)≤
        2*CompactFallbackAxisRun.volume D K0 ell q :=
  CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q level hc hK hD

/-- Partial actual node expression plus the true child callback sum. This pays
scalar groups, geometric child headers/PC and one completed exact return.
It does not cover child target stacks, spectator alignments, codec lifecycles
or all execution joins, and is not a complete node-runtime theorem. -/
theorem partial_node_with_callbacks {sh : Shape} {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (siteCount : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Call → Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell metadataP baseline : ℕ) (live : GroupIndex → ℕ)
    (headerCount descriptorRho descriptorLeft count slots right src dst : ℕ) (merge : Bool)
    (usedRows current target c : ℕ) (interchange : ℕ) (callbackCost : Call → ℕ)
    {I : ℝ} (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 1≤sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hp : 2*sh.bits≤metadataP) (hb : baseline≤metadataP-2*sh.bits)
    (hu : usedRows≤CompactComplexDenominatorCapacity.scalarRows)
    (hroom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
    (hlive : ∀ g,live g≤CompactComplexDenominatorCapacity.ledger
      CompactComplexDenominatorCapacity.scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows g.val).length)
    (hcurrent : current≤CompactComplexDenominatorCapacity.ledger
      CompactComplexDenominatorCapacity.scalarRows baseline levels frames returned usedRows)
    (ht : target≤current)
    (hi : (interchange : ℝ)≤I*(volume rows sh ell metadataP : ℝ)*
      ((arity^(k+2) : ℕ) : ℝ)^Parameters.tau) :
    ((scalarCost sh rows ell metadataP live+
      childGeometryCost siteCount rho visit ha pair rows+
      exactCost sh headerCount rows ell metadataP descriptorRho descriptorLeft count slots right src dst
        merge current target c+interchange+(calls.map callbackCost).sum : ℕ) : ℝ)≤
      ((partialConstant siteCount headerCount c : ℕ)+I)*(volume rows sh ell metadataP : ℝ)*
        ((arity^(k+2) : ℕ) : ℝ)^Parameters.tau+((calls.map callbackCost).sum : ℝ) := by
  have hs := scalar_linear_from_path path rows ell metadataP baseline live hr hp hb hroom hlive
  have hc := child_geometry_linear siteCount rho visit ha pair rows ell metadataP hr hG
  have he := exact_linear path headerCount rows ell metadataP descriptorRho descriptorLeft count slots right
    src dst merge hgroup hr (by omega) hA hK hp CompactComplexDenominatorCapacity.scalarRows
    baseline usedRows current target c hb hu hroom hcurrent ht
  have hw : 1≤arity^(k+2) := Nat.one_le_pow _ _ (by decide)
  have h := absorb_partial_local _ _ _ interchange (volume rows sh ell metadataP) (arity^(k+2))
    siteCount headerCount c hw hs hc he hi
  simpa only [Nat.cast_add] using add_le_add h (le_refl ((calls.map callbackCost).sum : ℝ))

end
end IntegerMultBounds.Machine.CompactComplexNodeLocalBudget
