module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedPackedStage

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
  obtain ⟨leafRate,install⟩ := installInvocationWorker
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
  have rootLe : c.node.width ≤ c.root.width := by
    have h := directoryDigits_bound prime c.root c.path
    unfold CutoffNodeInput.node
    omega
  have fits := (c.active.trans rootLe).trans_lt (Nat.lt_size_self _)
  have short : c.root.width.size ≤ c.node.width := by
    apply Nat.le_trans _ c.active
    apply Nat.size_le.mpr
    have space := alignedRootWidth_le c.root c.depth c.b c.cutoff c.levels c.base c.rootWidth c.stop
    have pos : 0 < c.root.width := c.rootWidth ▸ Nat.mul_pos (pow_pos (by decide : 0 < 64) c.depth) c.base
    omega
  have positive : 0 < c.stageWidth := by
    have h : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos c.idlePositive (by decide))
    rw [← c.stageCells] at h
    exact Nat.pos_of_mul_pos_left h
  let charged := fun i => time i+5000*V
  obtain ⟨seed,handoff⟩ := run charged (by
    intro i
    have smaller : (desc i).width < c.node.width := by
      change nodeChildren5[(child i).val]*(c.node.width/64) < c.node.width
      rw [c.width,Nat.mul_div_cancel_left _ (by decide)]
      exact Nat.mul_lt_mul_of_pos_right ((nodeChildren5_bounds _).2.trans_lt (by decide : 42 < 64)) (Nat.succ_pos _)
    have h := dispatch i c.node c.w c.stageWidth c.rowsPerStage c.root.width.size c.cutoff (budget (child i).val)
      c.width c.rows positive fits (Nat.size_le_size (smaller.le.trans rootLe)) (position i) (coords i) rate enough
      (fun above => by simpa only [active] using recurse i above)
    apply h.weaken
    have add := cutoffDispatchOverhead c.node c.w c.B c.stageFactor c.root.width.size c.width (child i) positive (position i)
    have card := Fintype.card_congr (position i)
    simp only [Fintype.card_fin] at card
    change volume prime (desc i) = V at card
    rw [show volume prime (scheduledChild prime c.node (child i)) = V from card,Nat.sub_eq_zero_of_le short] at add
    dsimp only [charged,time,stageBranchTime]
    rw [dite_eq_left (child i).isLt]
    let price := if c.cutoff < (desc i).width then budget (child i).val else
      ⌊rate*((desc i).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (desc i)⌋₊
    change price+4*c.w+23*(desc i).width+22*c.root.width.size+8*(CopyChildLayout.spectators (desc i)).size+61 ≤ price+5000*V
    change 4*c.w+23*(desc i).width+22*c.root.width.size+8*(CopyChildLayout.spectators (desc i)).size+61 ≤ 5000*V+22*0 at add
    omega)
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
