module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedPackedStage
import IntegerMultBounds.MathlibTM2.M6.BitStageChildDispatch

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Install stopped-leaf dispatch in each selected occurrence. Only the active
children require recursive execution contracts. -/
theorem dispatchedPackedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∃ leafRate : ℝ, ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ i, P → Pr (WorkerLabel P) (ts i) Q prime U) (f : I → P),
    ∃ body : ∀ i, WorkerLabel P → Pr (WorkerLabel P) (ts i) Q prime U, (∀ i g, body i (.active g) = large i g) ∧
    ∃ (T : ℕ) (src dst : Fin k ↪ Fin T) (host : I × WorkerLabel P → Pr (I × WorkerLabel P) T Q prime U)
      (code : Pr (I × WorkerLabel P) T Q prime U) (localCost : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (localCost w V : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧ ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    let time := stageBranchTime c.node c.cutoff rate budget
    (∀ i, c.cutoff < (desc i).width →
      if i.2.1 = 1 then ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (.active (f i)) (budget (child i).val) true
      else MoveOnBankExec c.node (desc i) c.w c.stageWidth (movePrefix.trans (ports i)) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (large i (f i)) (budget (child i).val) true) →
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let size : (prime^w)^128*W = V :=
      (ordinaryCompact_width _ _).symm.trans (by simp [V,W,CutoffNodeInput.stageWidth,Nat.mul_assoc,w])
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
      (localCost w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,qs,ports,build⟩ := initializedPackedStage n
  obtain ⟨leafRate,install⟩ := installStageWorker
  refine ⟨pre,post,ts,max qs (max columnCapacity stoppedCopyMachine.1),ports,leafRate,?_⟩
  intro P U Q cap large f
  let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
  have copy (i : I) : i.2.1 = 1 → ∃ j, child i = copyChildPosition (n,i.1,j) := by
    obtain ⟨p,j,i⟩ := i
    rintro rfl
    exact ⟨i,rfl⟩
  choose body active dispatch using fun i => install (ports i) ((Nat.le_max_right ..).trans cap) n i.1 i.2.1
    (child i) (copy i) (large i) (f i)
  obtain ⟨T,src,dst,host,code,work,⟨D,bound⟩,stage⟩ := build ((Nat.le_max_left ..).trans cap) body (fun _ => .entry)
  let length := (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length
  let localCost := fun w V => work w V+length*(5000*V)
  refine ⟨body,active,T,src,dst,host,code,localCost,⟨D+length*5000,?_⟩,?_⟩
  · intro w V hw hv
    have unit := Real.one_le_rpow (show (1 : ℝ) ≤ w by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
    have vol := le_mul_of_one_le_right (Nat.cast_nonneg V : (0 : ℝ) ≤ V) unit
    dsimp only [localCost]
    push_cast
    linarith only [bound w V hw hv,mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg length : (0 : ℝ) ≤ length)]
  intro c w V desc
  obtain ⟨position,coords,run⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget rate enough time recurse W size
  let charged := fun i => time i+5000*V
  obtain ⟨seed,handoff⟩ := run charged (fun i =>
    dispatch i c (position i) (coords i) budget rate enough (recurse i))
  refine ⟨seed,?_⟩
  let interval := List.range' (stageChildStart n) length
  have total : (interval.map charged).sum = (interval.map time).sum+length*(5000*V) := by
    simp only [charged,List.sum_map_add,List.map_const',List.sum_replicate,smul_eq_mul,interval,List.length_range']
  have price : localCost w V+(interval.map time).sum = work w V+(interval.map charged).sum := by
    rw [total]
    dsimp only [localCost]
    omega
  rw [price]
  exact handoff

end IntegerMultBounds.MathlibTM2.M6.BitNode
