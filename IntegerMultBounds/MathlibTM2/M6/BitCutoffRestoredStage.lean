module

public import IntegerMultBounds.MathlibTM2.M6.BitSelectedRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Once per invocation the sequence terminator costs one step. All recursive
budgets together form exactly the stage interval in the child directory. -/
theorem restoredStageBill {l r : ℕ} (n : Fin 9) (pre : StageRun → Fin l → MoveIndex)
    (post : StageRun → Fin r → MoveIndex) (first : ∀ p i, (pre p i).val = i.val)
    (last : ∀ p i, (post p i).val = l+i.val) (count : l+r = (Geometry.Moves.phaseEdges.filter positiveMove).length)
    (time : ℕ → ℕ) (work : (Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)) → ℕ) :
    let xs := (List.finRange 3).sigma fun j => List.finRange (invocationCounts l r j)
    let child := fun p j i => invocationChildren n p (pre p) (post p) j i
    (stageRuns.map fun p => (xs.map fun j => work ⟨p,j⟩ + time (child p j.1 j.2).val).sum+1).sum =
      (stageOccurrenceOrder l r |>.map work).sum+160+
      ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum := by
  intro xs child
  rw [List.sum_map_add,← stageOccurrenceChildSum n pre post first last count time]
  unfold stageOccurrenceOrder
  rw [sumSigmaCosts,sumSigmaCosts]
  simp only [xs,child,List.sum_map_add,List.map_const',List.sum_replicate,stageRuns_length,smul_eq_mul,Nat.mul_one]
  omega

/-- Compile the selected workers before choosing the node dimensions. On the archive
allocator's banks the restored stage then needs just the scheduled recursive calls. -/
theorem cutoffRestoredStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i))
      (data : ∀ i, Fin k ↪ Fin (ts i)),
    (∀ i (j : Fin (rowSwapBlock.tapes+35)), j.val ≠ 24 → ∀ h, data i h ≠ ports i j) ∧
    ∀ {P U : Type} {T Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P)
      (shared : Fin (k+1) ↪ Fin T) (bank : ∀ i, Fin (ts i+1) ↪ Fin T),
    let owners := fun i => withCutoffPort (data i)
    (∀ i j, bank i (owners i j) = shared j) →
    (∀ i l, (∀ j, owners i j ≠ l) → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) →
    let host := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (embProg (Fin.castAddEmb 1) id (body g.1 g.2))
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let fan := ((Fin.castAddEmb 1 (n := k)).trans shared).trans owner
    ∃ (rate : ℝ) (base swaps fixed : I → ℕ) (code : Pr (I × P) _ Q prime U), ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let desc := fun i => scheduledChild prime c.node (child i)
    let record := fun i : I => invocationWorkerRecord i.2.1 (desc i) c.root.width.size c.cutoff
    ∃ (position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V) (seed : ∀ i, Stacks (ts i+1) prime),
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    (∀ i, WorkerEntryWords (fun j => (scheduledRecordPorts (ports i) j).castAdd 1) (record i) (seed i)) ∧
    ∀ time : ℕ → ℕ, (∀ i, ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (record i)
      (position i) (body i) (f i) (time (child i).val) true) →
    ∀ x u S, HelperFan fan x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      S.R (owner (shared (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ i, PrivateTapes (owners i) (seed i) (embStk ((bank i).trans owner) S)) →
      ∃ z F t out, Exec (fun g => embProg owner id (host g)) code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          rate*((c.cells : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((stageOccurrenceOrder l r).map (fun i => (base i+swaps i*swapVolumeRate c.w)*c.cells+fixed i)).sum+160+
            ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan fan out F ∧ RestoredBorrowedStage n w c.B c.stageFactor x out := by
  intro l r I k
  obtain ⟨pre,post,first,last,workers⟩ := selectedStageWorkers n
  refine ⟨pre,post,?_⟩
  intro child
  obtain ⟨ts,qs,ports,data,off,build⟩ := cutoffWorkerFamily child (fun i => i.2.1)
    (fun i w B K => selectedOccurrenceEffect n w B K i.1 i.2.1 i.2.2) (fun i => workers i.1 i.2.1 i.2.2)
  refine ⟨ts,max qs columnCapacity,ports,data,off,?_⟩
  intro P U T Q cap body f shared bank owners aligned apart host scratch owner fan
  obtain ⟨base,swaps,fixed,worker,prepare⟩ := build ((Nat.le_max_left ..).trans cap) body f
  obtain ⟨rate,code,stage⟩ := selectedRestoredSweep n ((Nat.le_max_right ..).trans cap) (fun i => ts i+1)
    owners shared bank aligned apart (fun i g => embProg (Fin.castAddEmb 1) id (body i g)) worker
  refine ⟨rate,base,swaps,fixed,code,?_⟩
  intro c w V W desc record
  obtain ⟨position,coords,seed,entry,run⟩ := prepare c
  refine ⟨position,seed,coords,entry,?_⟩
  intro time recurse x u S live headers free cut stock
  let work := fun i => (base i+swaps i*swapVolumeRate c.w)*c.cells+fixed i
  have positive : 0 < V := by
    change 0 < (prime^(c.w+1))^16*c.stageWidth
    rw [c.stageCells]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  obtain ⟨z,F,t,y,exec,bill,user,out,done⟩ := stage w c.B c.stageFactor positive
    (fun i => work i+time (child i).val) seed (binSyms c.root.width.size c.cutoff)
    (run time recurse) x u S live headers free cut stock
  refine ⟨z,F,t,y,exec,?_,user,out,done⟩
  intro js nd
  have paid := bill js nd
  rw [restoredStageBill n pre post first last selectedPhaseCount time work] at paid
  simpa only [w,Nat.max_eq_right (Nat.succ_pos c.w),← c.stageCells,CutoffNodeInput.stageWidth,work] using paid

end IntegerMultBounds.MathlibTM2.M6.BitNode
