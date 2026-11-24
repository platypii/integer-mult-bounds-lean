module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

private theorem roundPacking {t held final start work children saved : ℕ} {packing : ℝ}
    (bill : ((t+held : ℕ) : ℝ)+final ≤ start+packing+work+((children+saved : ℕ) : ℝ)) :
    t+held+final ≤ start+((⌈packing⌉₊+work+children)+saved) := by
  exact_mod_cast (by push_cast at bill ⊢; linarith only [bill,Nat.le_ceil packing] :
    ((t+held+final : ℕ) : ℝ) ≤ ((start+((⌈packing⌉₊+work+children)+saved) : ℕ) : ℝ))

/-- Construct the packing headers from the parent descriptor before the selected stage. -/
theorem compactParentStage [M8.Machine.Net] (n : Fin 9) :
    let count := invocationCounts (selectedPhaseSchedule false).1.length (selectedPhaseSchedule true).1.length
    let slot := fun p => invocationChildren n p (selectedPhaseIndex false) (selectedPhaseIndex true)
    let coords := invocationIntervalPositions (phasePositions false) (phasePositions true)
    let J := Fin 32 × Fin 5
    ∃ (C : ℝ) (tapes : ∀ (_ : J) j, Fin (count j) → ℕ)
      (regs : ∀ p j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes p j i))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ p j i, P → Pr (Option (WorkerLabel P)) (tapes p j i) Q prime U)
      (f : ∀ (_ : J) j, Fin (count j) → P),
    ∃ body : ∀ p j i, Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) (tapes p j i) Q prime U,
    (∀ p j i g, body p j i (some (.active g)) = large p j i g) ∧
    let Label := Σ _ : J, (Σ j, Fin (count j) × Option (WorkerLabel P))
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let H := 80+((T+273)+LeafCore.small)
    ∃ (host : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (localRate : ℕ) (packRate : ℝ) (workers : Pr Empty (T+7) Q prime U),
    ∀ c : CutoffNodeInput,
      let w := c.w
      let W := c.stageWidth
      let V := (prime^(w+1))^16*W
      let child := fun p j i => scheduledChild prime c.node (slot p j i)
      ∃ pos : ∀ p j i, Fin (volume prime (child p j i)) ≃ Fin V,
      (∀ p j i, coords j i (child p j i) (w+1) W (pos p j i)) ∧
      ∀ (rate : ℝ) (time : ℕ → ℕ), C ≤ rate →
      let price := stageBranchTime c.node c.cutoff rate time
      (∀ p j i, c.cutoff < (child p j i).width → ScheduledChildExec c.node (child p j i) w W (regs p j i)
        (binSyms c.root.width.size c.cutoff) (pos p j i) (body p j i) (some (.active (f p j i))) (time (slot p j i).val) true) →
      ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
      PhaseSeedExec workers fan (160*(count 0+count 1+count 2)) c initial 960 ∧
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan ((fan.trans owner).trans stage) x S →
      ParentArchiveInput c.node w (embStk (archiveSetupPlacement 80 T LeafCore.small) S) →
      (∀ j : Fin LeafCore.small, S.L (stage (j.natAdd (T+273))) = [] ∧ S.R (stage (j.natAdd (T+273))) = []) →
      (∀ j, (∀ h, fan h ≠ j) → S.L (stage (owner j)) = initial.L j ∧ S.R (stage (owner j)) = initial.R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan ((fan.trans owner).trans stage) y F ∧
        RestoredBorrowedStage n (w+1) c.B c.stageFactor x y ∧
        ∀ js : List (Fin H), js.Nodup →
          ((t+tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) F) : ℕ) : ℝ)+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ : ℝ)+
            (localRate*c.cells : ℕ)+(((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum+
              tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) S) : ℕ) := by
  intro count slot coords J
  obtain ⟨C,tapes,regs,T,states,fan,build⟩ := compactSelectedStage n
  let headerStates := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨C,tapes,regs,T,max states headerStates,fan,?_⟩
  intro P U Q capacity large f
  obtain ⟨body,active,host,code,localRate,packRate,workers,run⟩ := build ((le_max_left ..).trans capacity) large f
  refine ⟨body,active,?_⟩
  intro Label scratch owner stage H
  let table := fun g : Label => embProg stage id (host g)
  let reserve := tapeCharge cleanupWeight (frameSlots fan)
  let stock := fun S : Stacks H prime => reserve (embStk (owner.trans stage) S)
  obtain ⟨setupRate,loader⟩ := parentArchiveThenWithCharge (U := U) ((le_max_right states headerStates).trans capacity)
  obtain ⟨setup,prepare⟩ := loader table (fun G price => price-stock G)
  refine ⟨table,setup.seq (embProg stage id code),setupRate+localRate,packRate,workers,?_⟩
  intro c w W V child
  obtain ⟨pos,geom,entry⟩ := run c
  refine ⟨pos,geom,?_⟩
  intro rate time enough price recursive shared
  obtain ⟨initial,view,init,execute⟩ := entry rate time enough recursive shared
  refine ⟨initial,view,init,?_⟩
  intro x u S live archive empty fresh
  let packing := ⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum
  let charge := packing+localRate*c.cells+children
  let post := fun F => ∃ y, HelperFan ((fan.trans owner).trans stage) y F ∧ RestoredBorrowedStage n (w+1) c.B c.stageFactor x y
  obtain ⟨z,F,t,exec,paid,user,y,ready,act⟩ := prepare c.node w c.B c.rowsPerStage c.width c.rows c.label c.stagePositive u S archive
    (embProg stage id code) ((charge : ℝ)+stock S) post (by
      intro v D headers keep leaf
      have held : stock D = stock S := by
        have left : D.L ∘ (owner.trans stage) = S.L ∘ (owner.trans stage) := funext fun j => (keep j).1
        have right : D.R ∘ (owner.trans stage) = S.R ∘ (owner.trans stage) := funext fun j => (keep j).2
        simp only [stock,reserve,tapeCharge,embStk,left,right]
      obtain ⟨z,F,m,exec,bill,user,out⟩ := chargedStageAfterSetup fan host code _ initial charge
        (RestoredBorrowedStage n (w+1) c.B c.stageFactor x) x reserve S live empty fresh (by
          intro v D live headers clean free
          obtain ⟨z,F,m,y,exec,user,ready,act,bill⟩ := execute x v D live headers clean free
          refine ⟨z,F,m,y,exec,?_,user,ready,act⟩
          intro js nd
          exact roundPacking (bill js nd)) v D headers keep leaf
      refine ⟨z,F,m,exec,?_,user,out⟩
      intro js nd
      have h := bill js nd
      change ((m+stock F : ℕ) : ℝ)+_ ≤ _+((charge+stock D : ℕ) : ℝ) at h
      rw [held] at h
      push_cast at h
      linarith)
  refine ⟨z,F,t,y,exec,user,ready,act,?_⟩
  intro js nd
  have h := paid js nd
  change (t : ℝ)+_ ≤ _+((setupRate*V : ℕ) : ℝ)+(_-stock F) at h
  change ((t+stock F : ℕ) : ℝ)+_ ≤ _+packing+(((setupRate+localRate)*c.cells : ℕ) : ℝ)+((children+stock S : ℕ) : ℝ)
  rw [show V = c.cells from c.stageCells] at h
  dsimp only [charge] at h
  push_cast at h ⊢
  rw [add_mul]
  rw [← show cleanupWeight = (fun l r => 4*l.length+2*r.length+4) from rfl] at h
  linarith only [h]

end IntegerMultBounds.MathlibTM2.M6.BitNode
