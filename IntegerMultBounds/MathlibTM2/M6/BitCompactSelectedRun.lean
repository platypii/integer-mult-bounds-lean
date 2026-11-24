module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactInvocation
public import IntegerMultBounds.MathlibTM2.M6.BitCompactInvocationSeed
public import IntegerMultBounds.MathlibTM2.M6.BitCompactComponents

/-! The compiled PR589 invocation with cutoff-dispatched children in inherited order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

def CompactRun [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (count : Fin 3 → ℕ)
    (slot : ∀ j, Fin (count j) → Fin nodeChildren5.length)
    (coords : ∀ j (_ : Fin (count j)) (child : Descriptor) (w W : ℕ),
      (Fin (volume prime child) ≃ Fin ((prime^w)^16*W)) → Prop) : Prop :=
  ∃ (C : ℝ) (tapes : ∀ j, Fin (count j) → ℕ) (regs : ∀ j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j i))
    (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T),
  ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ j i, P → Pr (Option (WorkerLabel P)) (tapes j i) Q prime U) (f : ∀ j, Fin (count j) → P),
    ∃ (body : ∀ j i, Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) (tapes j i) Q prime U),
    (∀ j i g, body j i (some (.active g)) = large j i g) ∧
    let Label := Σ j, Fin (count j) × Option (WorkerLabel P)
    ∃ (host : Label → Pr Label T Q prime U) (code : Pr Label T Q prime U) (localRate : ℕ) (setup : Pr Empty (T+7) Q prime U),
    ∀ c : CutoffNodeInput,
      let w := c.w
      let W := c.stageWidth
      let V := (prime^(w+1))^16*W
      let child := fun j i => scheduledChild prime c.node (slot j i)
      ∃ pos : ∀ j i, Fin (volume prime (child j i)) ≃ Fin V,
      (∀ j i, coords j i (child j i) (w+1) W (pos j i)) ∧
      ∀ shared : Stacks (142081+2) prime, ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      PhaseSeedExec setup fan (count 0+count 1+count 2) c prepared 6 ∧
      ∀ (rate : ℝ) (time : ℕ → ℕ), C ≤ rate →
      let price := stageBranchTime c.node c.cutoff rate time
      (∀ j i, c.cutoff < (child j i).width → ScheduledChildExec c.node (child j i) w W (regs j i)
        (binSyms c.root.width.size c.cutoff) (pos j i) (body j i) (some (.active (f j i))) (time (slot j i).val) true) →
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          (((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map price).sum+
            localRate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧ HelperFan fan y F ∧
        BorrowedStep n (w+1) ((prime^(w+1))^112*c.B) c.stageFactor p x y

private theorem compileRun [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5)
    (count : Fin 3 → ℕ) (slot : ∀ j, Fin (count j) → Fin nodeChildren5.length) (coords)
    (parts : ∀ j, CompactComponent n p j (count j) (slot j) (coords j))
    (bill : ∀ time : ℕ → ℕ, let fee := fun j => (List.ofFn (fun i => time (slot j i).val)).sum
      fee 0+(fee 1+fee 2) = ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum) :
    CompactRun n p count slot coords := by
  classical
  choose C tapes regs ts qs owners place build using parts
  obtain ⟨T,fan,bank,_,cover,apart,assemble⟩ := compactInvocation_host n p ts owners
  refine ⟨∑ j, |C j|,tapes,regs,T,Finset.univ.sup qs,fan,?_⟩
  intro P U Q cap large f
  choose body active code localRate loaders run using fun j =>
    build j ((Finset.le_sup (Finset.mem_univ j)).trans cap) (large j) (f j)
  refine ⟨body,active,?_⟩
  intro Label
  let worker := fun j (g : Fin (count j) × Option (WorkerLabel P)) =>
    embProg (place j g.1) (Prod.mk g.1) (body j g.1 g.2)
  let host : Label → Pr Label T Q prime U := fun g => embProg (bank g.1) (fun h => (⟨g.1,h⟩ : Label)) (worker g.1 g.2)
  obtain ⟨program,execute⟩ := assemble worker code
  obtain ⟨setup,load⟩ := invocationSeed ts count fan owners bank cover apart loaders
  refine ⟨host,program,localRate 0+(localRate 1+localRate 2),setup,?_⟩
  intro c w W V child
  choose pos geom prepare using fun j => run j c
  refine ⟨pos,geom,?_⟩
  intro shared
  choose seed views init steps using fun j => prepare j shared
  obtain ⟨prepared,view,stock,go⟩ := execute (w+1) ((prime^(w+1))^112*c.B) c.stageFactor shared seed
  refine ⟨prepared,view,load c seed prepared stock init,?_⟩
  intro rate time enough price recurse x u S ready fresh
  let fee := fun j => (List.ofFn fun i => price (slot j i).val).sum
  obtain ⟨z,F,t,y,exec,user,paid,out,effect⟩ := go (fun j => fee j+localRate j*c.cells) (fun j => by
    have room : C j ≤ rate := ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ j))).trans enough
    have h := steps j rate (fun i => time (slot j i).val) room (recurse j)
    simpa only [fee,price,stageBranchTime,dite_eq_left (slot j _).isLt,Fin.eta,w,worker,CutoffNodeInput.stageWidth] using h) x u S ready fresh
  refine ⟨z,F,t,y,exec,user,workerCost.weaken (charged := true) paid ?_,out,effect⟩
  apply Nat.add_le_add_right
  have fees := bill price
  change fee 0+(fee 1+fee 2) = _ at fees
  rw [← fees,Nat.add_mul,Nat.add_mul]
  omega

def RunCoordinates (k : ℕ) := ∀ (_ : Fin k) (child : Descriptor) (w W : ℕ),
  (Fin (volume prime child) ≃ Fin ((prime^w)^16*W)) → Prop

def invocationIntervalPositions {l r : ℕ} (pre : RunCoordinates l) (post : RunCoordinates r) :
    ∀ j, RunCoordinates (invocationCounts l r j) :=
  invocationSlots (α := fun j => RunCoordinates (invocationCounts l r j))
    pre (fun _ => CopyIntervalPositions) post

private theorem compileThree [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) {l r : ℕ}
    (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex) (a : RunCoordinates l) (b : RunCoordinates r)
    (left : CompactComponent n p 0 l (fun j => phaseChildPositions.choose (n,p,pre j)) a)
    (right : CompactComponent n p 2 r (fun j => phaseChildPositions.choose (n,p,post j)) b)
    (bill : ∀ time : ℕ → ℕ,
      (List.ofFn (fun j => time (phaseChildPositions.choose (n,p,pre j)).val)).sum +
        ((List.ofFn (fun j : CopyIndex => time (copyChildPosition (n,p,j)).val)).sum +
         (List.ofFn (fun j => time (phaseChildPositions.choose (n,p,post j)).val)).sum) =
      ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum) :
    CompactRun n p (invocationCounts l r) (invocationChildren n p pre post) (invocationIntervalPositions a b) :=
  compileRun n p _ _ _ (invocationSlots left (compactCopyComponent n p) right) bill

/-- Both scalar phases and all nine COPY windows execute on a common bank. -/
theorem compactSelectedRun [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    CompactRun n p (invocationCounts l r)
      (invocationChildren n p (selectedPhaseIndex false) (selectedPhaseIndex true))
      (invocationIntervalPositions (phasePositions false) (phasePositions true)) := by
  intro l r
  exact compileThree n p (selectedPhaseIndex false) (selectedPhaseIndex true) (phasePositions false)
    (phasePositions true) (compactPhaseComponent n p false) (compactPhaseComponent n p true) (compactInvocation_bill n p)

end IntegerMultBounds.MathlibTM2.M6.BitNode
