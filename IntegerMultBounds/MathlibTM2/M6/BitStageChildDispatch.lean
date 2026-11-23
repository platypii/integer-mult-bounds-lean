module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Install one selected stage worker and absorb its dispatch overhead into the
stage volume. The caller supplies execution only for children above the cutoff. -/
theorem installStageWorker [M8.Machine.Net] :
    ∃ leafRate : ℝ, ∀ {P U : Type} {T Q : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (_cap : max columnCapacity stoppedCopyMachine.1 ≤ Q) (n : Fin 9) (p : StageRun)
      (j : Fin 3) (k : Fin nodeChildren5.length), (j = 1 → ∃ i, k = copyChildPosition (n,p,i)) →
      ∀ (large : P → Pr (WorkerLabel P) T Q prime U) (f : P),
      ∃ body : WorkerLabel P → Pr (WorkerLabel P) T Q prime U,
      (∀ g, body (.active g) = large g) ∧
      ∀ (c : CutoffNodeInput), let desc := scheduledChild prime c.node k
      let V := (prime^(c.w+1))^16*c.stageWidth
      ∀ (position : Fin (volume prime desc) ≃ Fin V), invocationCoordinates j (c.w+1) c.stageWidth position →
      ∀ (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
      let time := stageBranchTime c.node c.cutoff rate budget
      let header := binSyms (A := prime) c.root.width.size c.cutoff
      (c.cutoff < desc.width → if j = 1 then ScheduledChildExec c.node desc c.w c.stageWidth ports header
        position body (.active f) (budget k.val) true else MoveOnBankExec c.node desc c.w c.stageWidth
        (movePrefix.trans ports) header position body (large f) (budget k.val) true) →
      ScheduledChildExec c.node desc c.w c.stageWidth ports (invocationWorkerRecord j desc c.root.width.size c.cutoff)
        position body .entry (time k.val+5000*V) true := by
  obtain ⟨leafRate,install⟩ := installInvocationWorker
  refine ⟨leafRate,?_⟩
  intro P U T Q ports cap n p j k copy large f
  obtain ⟨body,active,dispatch⟩ := install ports cap n p j k copy large f
  refine ⟨body,active,?_⟩
  intro c desc V position coords budget rate enough time header recurse
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
  have smaller : desc.width < c.node.width := by
    change nodeChildren5[k.val]*(c.node.width/64) < c.node.width
    rw [c.width,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.mul_lt_mul_of_pos_right ((nodeChildren5_bounds _).2.trans_lt (by decide : 42 < 64)) (Nat.succ_pos _)
  have h := dispatch c.node c.w c.stageWidth c.rowsPerStage c.root.width.size c.cutoff (budget k.val)
    c.width c.rows positive fits (Nat.size_le_size (smaller.le.trans rootLe)) position coords rate enough
    (fun above => by simpa only [active] using recurse above)
  apply h.weaken
  have add := cutoffDispatchOverhead c.node c.w c.B c.stageFactor c.root.width.size c.width k positive position
  have card := Fintype.card_congr position
  simp only [Fintype.card_fin] at card
  change volume prime desc = V at card
  rw [show volume prime (scheduledChild prime c.node k) = V from card,Nat.sub_eq_zero_of_le short] at add
  dsimp only [time,stageBranchTime]
  rw [dite_eq_left k.isLt]
  let price := if c.cutoff < desc.width then budget k.val else
    ⌊rate*(desc.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime desc⌋₊
  change price+4*c.w+23*desc.width+22*c.root.width.size+8*(CopyChildLayout.spectators desc).size+61 ≤ price+5000*V
  change 4*c.w+23*desc.width+22*c.root.width.size+8*(CopyChildLayout.spectators desc).size+61 ≤ 5000*V+22*0 at add
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
