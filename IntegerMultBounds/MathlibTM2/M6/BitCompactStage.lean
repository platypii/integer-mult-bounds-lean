module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactSelectedRun

/-! Run the compact invocation family through helper packing and final restoration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- The invocation work is linear in the stage volume. The width-dependent
packing and restoration cost is kept separate from the exact child bill. -/
def CompactStage [M8.Machine.Net] (n : Fin 9) (count : Fin 3 → ℕ)
    (slot : ∀ (_ : Fin 32 × Fin 5) j, Fin (count j) → Fin nodeChildren5.length)
    (coords : ∀ j (_ : Fin (count j)) (child : Descriptor) (w W : ℕ),
      (Fin (volume prime child) ≃ Fin ((prime^w)^16*W)) → Prop) : Prop :=
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
    let H := (T+273)+LeafCore.small
    ∃ (host : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (localRate : ℕ) (packRate : ℝ),
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
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (fan.trans owner) x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView (w+1) 1 (c.B*prime^(64*((w+1)*64))*c.stageFactor) i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ j, (∀ h, fan h ≠ j) → S.L (owner j) = initial.L j ∧ S.R (owner j) = initial.R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan (fan.trans owner) y F ∧
        RestoredBorrowedStage n (w+1) c.B c.stageFactor x y ∧
        ∀ js : List (Fin H), js.Nodup →
          ((t+tapeCharge cleanupWeight (frameSlots fan) (embStk owner F) : ℕ) : ℝ)+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+packRate*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+
            (localRate*c.cells : ℕ)+(((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map price).sum+
              tapeCharge cleanupWeight (frameSlots fan) (embStk owner S) : ℕ)

private theorem compactRestoredStage [M8.Machine.Net] (n : Fin 9) (count : Fin 3 → ℕ)
    (slot : ∀ (_ : Fin 32 × Fin 5) j, Fin (count j) → Fin nodeChildren5.length) (coords)
    (runs : ∀ p, CompactRun n p count (slot p) coords) : CompactStage n count slot coords := by
  classical
  unfold CompactStage
  intro J
  have weightEq : cleanupWeight = (fun l r => 4*l.length+2*r.length+4) := rfl
  choose C tapes regs ts qs owners build using runs
  let observed := (List.finRange (142081+2)).reverse
  have unique : observed.Nodup := List.nodup_reverse.2 (List.nodup_finRange _)
  obtain ⟨T,fan,banks,assemble⟩ := allocatedArchiveSweepWithCharge n ts owners ⟨observed,unique⟩
  refine ⟨∑ p, |C p|,tapes,regs,T,max (Finset.univ.sup qs) columnCapacity,fan,?_⟩
  intro P U Q cap large f
  choose body active worker call localRate run using fun p => build p
    ((Finset.le_sup (Finset.mem_univ p)).trans ((le_max_left ..).trans cap)) (large p) (f p)
  refine ⟨body,active,?_⟩
  intro Label scratch owner H
  let inner := fun g : Label => embProg (banks g.1) (fun f => (⟨g.1,f⟩ : Label)) (worker g.1 g.2)
  let host : Label → Pr Label H Q prime U := fun g => embProg owner id (inner g)
  obtain ⟨packRate,make⟩ := assemble ((le_max_right ..).trans cap) worker
  obtain ⟨code,execute⟩ := make call
  refine ⟨host,code,(stageRuns.map localRate).sum,packRate,?_⟩
  intro c w W V child
  choose pos geom prepare using fun p => run p c
  refine ⟨pos,geom,?_⟩
  intro rate time enough price recurse shared
  have positive : 0 < V := by
    rw [show V = c.cells from c.stageCells]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  have slots {N : ℕ} (ports : Fin (142081+2) ↪ Fin N) : observed.map ports = frameSlots ports := by
    simp only [observed,List.map_reverse,frameSlots]
  obtain ⟨initial,view,stage⟩ := execute (w+1) c.B c.stageFactor positive (fun p => localRate p*c.cells) price
    (fun p shared => by
      obtain ⟨seed,view,step⟩ := prepare p shared
      refine ⟨seed,view,?_⟩
      intro a v D ready fresh
      have threshold : C p ≤ rate := ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ p))).trans enough
      obtain ⟨z,F,m,b,exec,user,paid,out,act⟩ := step rate time threshold (recurse p) a v D ready fresh
      refine ⟨z,F,m,b,exec,?_,user,out,act⟩
      intro js nd
      rw [slots]
      simpa only [weightEq,price,Nat.add_comm (localRate p*c.cells)] using paid js nd) shared
  refine ⟨initial,view,?_⟩
  intro x u S ready headers clean free
  obtain ⟨z,F,t,y,exec,paid,user,out,act⟩ := stage x u S ready headers clean free
  refine ⟨z,F,t,y,exec,user,out,act,?_⟩
  intro js nd
  have h := paid js nd
  simpa only [slots,List.sum_map_mul_right,max_eq_right (show 1 ≤ w+1 by omega),weightEq,V,W,w,owner,scratch,CutoffNodeInput.stageWidth] using h

/-- The physical stage runs every selected invocation and restores the helper coordinates. -/
theorem compactSelectedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    CompactStage n (invocationCounts l r)
      (fun p => invocationChildren n p (selectedPhaseIndex false) (selectedPhaseIndex true))
      (invocationIntervalPositions (phasePositions false) (phasePositions true)) := by
  intro l r
  exact compactRestoredStage n _ _ _ (compactSelectedRun n)

end IntegerMultBounds.MathlibTM2.M6.BitNode
