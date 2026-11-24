module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactParentStage
public import IntegerMultBounds.MathlibTM2.M6.BitStageCallerLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

private theorem integralStageBill {t fg fs packing work children saved : ℕ}
    (h : (t : ℝ)+fg ≤ fs+(packing : ℝ)+work+((children+saved : ℕ) : ℝ)) :
    t+fg ≤ fs+(packing+work+(children+saved)) := by
  exact_mod_cast (by push_cast at h ⊢; linarith only [h] :
    ((t+fg : ℕ) : ℝ) ≤ ((fs+(packing+work+(children+saved)) : ℕ) : ℝ))

/-- Run the selected stage from the six descriptor words on the caller bank. -/
theorem compactDescriptorStage [M8.Machine.Net] (n : Fin 9) :
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
    let place := Fin.castAddEmb 37 (n := H)
    ∃ (host : Label → Pr Label (H+37) Q prime U) (code : Pr Label (H+37) Q prime U) (localRate : ℕ) (packRate : ℝ) (workers : Pr Empty (T+7) Q prime U),
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
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan ((fan.trans owner).trans stage) x (embStk place S) →
      (∀ i : Fin 37, S.R (i.natAdd H) = callerHeaderBank (fun j => (Routines.hdr c.node j).map bitSymbol) i) →
      (∀ j, let k := place (archiveSetupPlacement 80 T LeafCore.small j); S.L k = [] ∧ S.R k = []) →
      (∀ j : Fin LeafCore.small, (embStk place S).L (stage (j.natAdd (T+273))) = [] ∧ (embStk place S).R (stage (j.natAdd (T+273))) = []) →
      (∀ j, (∀ h, fan h ≠ j) → (embStk place S).L (stage (owner j)) = initial.L j ∧ (embStk place S).R (stage (owner j)) = initial.R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan ((fan.trans owner).trans stage) y (embStk place F) ∧
        RestoredBorrowedStage n (w+1) c.B c.stageFactor x y ∧
        ∀ js : List (Fin (H+37)), js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place F))+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
            localRate*c.cells+(((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum)+
            tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place S)) := by
  intro count slot coords J
  obtain ⟨C,tapes,regs,T,states,fan,build⟩ := compactParentStage n
  refine ⟨C,tapes,regs,T,states,fan,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,host,code,localRate,packRate,workers,run⟩ := build cap large f
  refine ⟨body,active,?_⟩
  intro Label scratch owner stage H place
  let table := fun g : Label => embProg place id (host g)
  obtain ⟨setup,load⟩ := compactCallerArchive (T := T) (R := LeafCore.small) table
  refine ⟨table,setup.seq (embProg place id code),314*142080+localRate,packRate,workers,?_⟩
  intro c w W V child
  obtain ⟨pos,geom,entry⟩ := run c
  refine ⟨pos,geom,?_⟩
  intro rate time enough price recurse shared
  obtain ⟨initial,view,init,execute⟩ := entry rate time enough recurse shared
  refine ⟨initial,view,init,?_⟩
  intro x u S live words free empty fresh
  obtain ⟨v,D,a,start,user,setupBill,archive,frame⟩ := load c u S words free
  have kept j := frame (stage (owner j)) (fun i => (archiveSetupPlacement_frame (R := 80) (T := T) (L := LeafCore.small) i).1 j)
  have leaf (j : Fin LeafCore.small) := frame (stage (j.natAdd (T+273))) (fun i => (archiveSetupPlacement_frame (R := 80) (T := T) (L := LeafCore.small) i).2 j)
  have step := execute x (embDn place v) (embStk place D)
  have mid := (helperFan_of_agree (fan := (fan.trans owner).trans stage) (S := embStk place S) (F := embStk place D) live (fun i => kept (fan i)))
  dsimp only [owner,stage,scratch] at mid
  have active := step mid archive
  obtain ⟨z,F,b,y,exec,same,ready,act,bill⟩ := active
    (fun j => ⟨(leaf j).1.trans (empty j).1,(leaf j).2.trans (empty j).2⟩)
    (fun j off => ⟨(kept j).1.trans (fresh j off).1,(kept j).2.trans (fresh j off).2⟩)
  obtain ⟨z',G,placed,_,last,seen,off⟩ := exec_emb (ι := id) (body := host) (body' := table) (e := place) place.injective
    (fun _ => rfl) exec v rfl D rfl
  subst F
  refine ⟨z',G,a+b,y,?_,?_,?_,?_,?_⟩
  · exact start.seq placed
  · simp only [embDn] at same
    exact last.trans (same.trans user)
  · dsimp only [owner,stage,scratch]; exact ready
  · exact act
  let stock := fun A : Stacks (H+37) prime => tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place A))
  have held : stock D = stock S := by
    have left : (D.L ∘ place) ∘ (owner.trans stage) = (S.L ∘ place) ∘ (owner.trans stage) := funext fun j => (kept j).1
    have right : (D.R ∘ place) ∘ (owner.trans stage) = (S.R ∘ place) ∘ (owner.trans stage) := funext fun j => (kept j).2
    simp only [stock,tapeCharge,embStk,left,right]
  let packing := ⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum
  intro js distinct
  have charge := placedCleanup_cost_le place D G cleanupWeight (b+stock G)
    (packing+localRate*c.cells+(children+stock D)) off (by
      intro is nd
      exact integralStageBill (bill is nd)) js distinct
  have init := setupBill js distinct
  rw [held] at charge
  change a+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+314*volume prime c.node at init
  rw [← c.cells_share,← Nat.mul_assoc,Nat.mul_right_comm 314 c.cells 142080] at init
  change a+b+stock G+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+packing+(314*142080+localRate)*c.cells+children+stock S
  rw [Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
