module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactCopySweep
public import IntegerMultBounds.MathlibTM2.M6.BitCompactPhase

/-! A common execution contract for the three compiled PR589 invocation components. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

def CompactComponent [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (part : Fin 3)
    (count : ℕ) (slot : Fin count → Fin nodeChildren5.length)
    (coords : ∀ (_ : Fin count) (child : Descriptor) (w W : ℕ),
      (Fin (volume prime child) ≃ Fin ((prime^w)^16*W)) → Prop) : Prop :=
    let J := Fin count
    ∃ (C : ℝ) (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ j, P → Pr (Option (WorkerLabel P)) (tapes j) Q prime U) (f : J → P),
    ∃ body : ∀ j, Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) (tapes j) Q prime U,
    (∀ j g, body j (some (.active g)) = large j g) ∧
    let host := fun g : J × Option (WorkerLabel P) => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    ∃ (code : Pr (J × Option (WorkerLabel P)) T Q prime U) (localRate : ℕ) (setup : Pr Empty (T+7) Q prime U), ∀ c : CutoffNodeInput,
      let w := c.w
      let K := c.stageFactor
      let blocks := (prime^(w+1))^112*c.B
      let W := c.stageWidth
      let V := (prime^(w+1))^16*W
      let child := fun j => scheduledChild prime c.node (slot j)
      ∃ position : ∀ j, Fin (volume prime (child j)) ≃ Fin V,
      (∀ j, coords j (child j) (w+1) W (position j)) ∧
      ∀ shared : Stacks (142081+2) prime, ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      PhaseSeedExec setup fan count c prepared ∧
      ∀ (rate : ℝ) (recursiveTime : J → ℕ), C ≤ rate →
      let price := fun j => if c.cutoff < (child j).width then recursiveTime j else
        ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
      (∀ j, c.cutoff < (child j).width → ScheduledChildExec c.node (child j) w W (regs j)
        (binSyms c.root.width.size c.cutoff) (position j) (body j) (some (.active (f j))) (recursiveTime j) true) →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u (S : Stacks T prime), HelperFan fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          ((List.ofFn price).sum+localRate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧ HelperFan fan out F ∧
        InvocationComponentEffect n p (w+1) blocks K part data out

noncomputable def selectedInterval (b : Bool) (j : Fin (selectedPhaseSchedule b).1.length) :
    ℕ × ℕ :=
  let i := selectedPhaseIndex b j
  let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
  let a := Geometry.Dimensions.value edge.1
  let d := Geometry.Dimensions.value edge.2
  (min a d,max a d)

def phasePositions (b : Bool) (j : Fin (selectedPhaseSchedule b).1.length)
    (child : Descriptor) (w W : ℕ) (position : Fin (volume prime child) ≃ Fin ((prime^w)^16*W)) : Prop :=
  let e := selectedInterval b j
  let lane := phaseIntervalChild e.1 e.2 w W
  ∃ size, InheritedIntervalPositions child lane size position

theorem compactPhaseComponent [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (b : Bool) :
    CompactComponent n p (if b then 2 else 0) (selectedPhaseSchedule b).1.length
      (fun j => phaseChildPositions.choose (n,p,selectedPhaseIndex b j)) (phasePositions b) := by
  obtain ⟨C,tapes,regs,T,states,fan,bank,build⟩ := compactPhase n p b
  refine ⟨C,tapes,regs,T,states,fan,bank,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,code,rate,setup,run⟩ := build cap large f
  refine ⟨body,active,code,rate,setup,?_⟩
  intro c w K blocks W V child
  obtain ⟨pos,size,coords,prepare⟩ := run c
  refine ⟨pos,fun j => ⟨size j,coords j⟩,?_⟩
  intro shared
  obtain ⟨seed,view,load,execute⟩ := prepare shared
  refine ⟨seed,view,load,?_⟩
  intro leafRate time enough price recurse x u S ready fresh
  obtain ⟨z,F,t,exec,user,paid,out⟩ := execute leafRate time enough recurse x u S ready fresh
  refine ⟨z,F,t,_,exec,user,paid,out,?_⟩
  cases b <;> rfl

theorem compactCopyComponent [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    CompactComponent n p 1 Copy.lifecycles.length (fun j => copyChildPosition (n,p,j))
      (fun _ => CopyIntervalPositions) := compactCopySweep n p

end IntegerMultBounds.MathlibTM2.M6.BitNode
