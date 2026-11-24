module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactDescriptorStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- Initialize all private workers and execute the stage from descriptor and dimension words. -/
theorem compactInitializedStage [M8.Machine.Net] (n : Fin 9) :
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
    let outer := Fin.castAddEmb 7 (n := H+37)
    let ext := Fin.natAddEmb (H+37) (m := 7)
    ∃ (host : Label → Pr Label ((H+37)+7) Q prime U) (code : Pr Label ((H+37)+7) Q prime U) (localRate : ℕ) (packRate : ℝ),
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
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan ((fan.trans owner).trans stage) x (embStk place (embStk outer S)) →
      (∀ i : Fin 37, (embStk outer S).R (i.natAdd H) = callerHeaderBank (fun j => (Routines.hdr c.node j).map bitSymbol) i) →
      (∀ j, let k := place (archiveSetupPlacement 80 T LeafCore.small j); (embStk outer S).L k = [] ∧ (embStk outer S).R k = []) →
      (∀ j : Fin LeafCore.small, (embStk place (embStk outer S)).L (stage (j.natAdd (T+273))) = [] ∧ (embStk place (embStk outer S)).R (stage (j.natAdd (T+273))) = []) →
      (∀ j, (∀ h, fan h ≠ j) → (embStk place (embStk outer S)).L (stage (owner j)) = [] ∧ (embStk place (embStk outer S)).R (stage (owner j)) = []) →
      S.R (ext 0) = binSyms (prime^(w+1)).size (prime^(w+1)) → S.R (ext 1) = binSyms W.size W →
      S.R (ext 2) = binSyms 1 1 → S.R (ext 3) = binSyms (w+1).size (w+1) →
      S.R (ext 4) = [] → S.R (ext 5) = [] → S.R (ext 6) = binSyms c.root.width.size c.cutoff →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan ((fan.trans owner).trans stage) y (embStk place (embStk outer F)) ∧
        RestoredBorrowedStage n (w+1) c.B c.stageFactor x y ∧
        ∀ js : List (Fin ((H+37)+7)), js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place (embStk outer F)))+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
            localRate*c.cells+(((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum)+
            tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place (embStk outer S))) := by
  intro count slot coords J
  obtain ⟨C,tapes,regs,T,states,fan,build⟩ := compactDescriptorStage n
  refine ⟨C,tapes,regs,T,states,fan,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,host,code,localRate,packRate,workers,run⟩ := build cap large f
  refine ⟨body,active,?_⟩
  intro Label scratch owner stage H place outer ext
  let data := (((owner.trans stage).trans place).trans outer)
  let table := fun g : Label => embProg outer id (host g)
  let k := 160*(count 0+count 1+count 2)
  have separate (j : Fin T) (s : Fin 7) : data j ≠ ext s := by
    intro eq
    have h := congrArg Fin.val eq
    change (place (stage (owner j))).val = H+37+s.val at h
    omega
  let ports := appendPorts data ext separate
  refine ⟨table,(embProg ports Empty.elim workers).seq (embProg outer id code),320*k+960+localRate,packRate,?_⟩
  intro c w W V child
  obtain ⟨pos,geom,entry⟩ := run c
  refine ⟨pos,geom,?_⟩
  intro rate time enough price recurse x u S live words free empty blank modulus spectator unit atom ht hs cut
  obtain ⟨initial,_,init,execute⟩ := entry rate time enough recurse (embStk (fan.trans data) S)
  have load := init.place table ports u S
  simp only [ports,appendPorts,Function.Embedding.trans_apply,Function.Embedding.coeFn_mk,
    Fin.castAddEmb_apply,Fin.natAddEmb_apply,Fin.addCases_left,Fin.addCases_right] at load
  obtain ⟨v,D,a,start,user,setupBill,stock,frame⟩ := load modulus spectator unit atom ht hs cut blank
  have ownerKeep h := frame (data (fan h)) (fun l off => data.injective.ne (Ne.symm (off h)))
  have outside j (off : ∀ l, place (stage (owner l)) ≠ j) :=
    frame (outer j) (fun l _ => outer.injective.ne (off l))
  have input (i : Fin 37) := outside (i.natAdd H) (fun l eq => by
    have h := congrArg Fin.val eq
    change (stage (owner l)).val = H+i.val at h
    omega)
  have archive i := outside (place (archiveSetupPlacement 80 T LeafCore.small i))
    (fun l => place.injective.ne (Ne.symm ((archiveSetupPlacement_frame i).1 l)))
  have leaf (j : Fin LeafCore.small) := outside (place (stage (j.natAdd (T+273)))) (fun l =>
    place.injective.ne (stage.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change (l.castAdd 273).val = T+273+j.val at h
      omega)))
  have mid := helperFan_of_agree (fan := (fan.trans owner).trans stage)
    (S := embStk place (embStk outer S)) (F := embStk place (embStk outer D)) live ownerKeep
  dsimp only [owner,stage,scratch] at mid
  obtain ⟨z,F,b,y,exec,same,ready,act,bill⟩ := execute x (embDn outer v) (embStk outer D) mid
    (fun i => (input i).2.trans (words i))
    (fun i => ⟨(archive i).1.trans (free i).1,(archive i).2.trans (free i).2⟩)
    (fun i => ⟨(leaf i).1.trans (empty i).1,(leaf i).2.trans (empty i).2⟩) stock
  obtain ⟨z',G,placed,_,last,seen,off⟩ := exec_emb (ι := id) (body := host) (body' := table)
    outer.injective (fun _ => rfl) exec v rfl D rfl
  subst F
  refine ⟨z',G,a+b,y,?_,?_,?_,act,?_⟩
  · apply Exec.seq _ placed
    simpa only [ports,appendPorts,Function.Embedding.coeFn_mk] using start
  · simp only [embDn] at same
    exact last.trans (same.trans user)
  · dsimp only [owner,stage,scratch]; exact ready
  let reserve := fun A : Stacks ((H+37)+7) prime =>
    tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place (embStk outer A)))
  have held : reserve D = reserve S := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro j mem
    obtain ⟨h,rfl⟩ := (mem_frameSlots fan j).mp mem
    exact congrArg₂ cleanupWeight (ownerKeep h).1 (ownerKeep h).2
  let packing := ⌈packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum
  intro js nd
  have charge := placedCleanup_cost_le outer D G cleanupWeight (b+reserve G)
    (packing+localRate*c.cells+children+reserve D) off (fun is distinct => by
      have h := bill is distinct
      change b+reserve G+_ ≤ _+packing+localRate*c.cells+children+reserve D at h
      omega) js nd
  rw [held] at charge
  have paid := setupBill js nd
  rw [cut] at paid
  have bound := stageWorkerSeedCost c k 960
  change a+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+_ at paid
  change a+b+reserve G+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+packing+
    (320*k+960+localRate)*c.cells+children+reserve S
  rw [Nat.add_mul]
  change a+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+
    (178*k*c.cells+k*(8*(binSyms (A := prime) c.root.width.size c.cutoff).length+6)+960) at paid
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
