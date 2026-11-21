module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedScan
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner

/-! Run a parent chart and the recursive directory stage on their shared owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem chartDirectory_exec [M8.Machine.Net] {T k R W w parents : ℕ} {P U : Type}
    (interval : ℕ × ℕ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (records : R = parents*(prime^(w+1))^(64*64)) (upper : interval.2 ≤ 63) :
    let M := prime^(w+1)
    let N := M^128*W
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    ∀ (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := R*N))) (src : Fin k)
      (metadata : ℕ → List (Fin (prime+4))) (words : Fin k → Fin (R*N) → ZMod 2),
    let routed := stage.transform words src
    let slot := (0 : Fin 5).natAdd T
    let placement := payloadPlacement slot (stage.slots src)
    let chart : Fin stage.tapes ↪ Fin ((T+5)+stage.tapes) := Fin.natAddEmb (T+5)
    ∀ (restore : ∀ x, stage.output x = stage.input (stage.transform x))
      (body : P → Pr P (T+5) columnCapacity prime U) (program : Pr P (T+5) columnCapacity prime U)
      (budget capacity : ℕ) (chartFits : stage.states ≤ capacity) (fits : columnCapacity ≤ capacity)
      (u : HS ((T+5)+stage.tapes) capacity prime U) (S : Stacks stage.tapes prime)
      (finished : Stacks (T+5) prime → Prop),
    RepT (stage.input words) S.L S.R →
    (∀ (a : HS (T+5) columnCapacity prime U) (F : Stacks stage.tapes prime),
      RepT (phaseOwners (stage.transform words)) (embStk stage.slots F).L (embStk stage.slots F).R →
      ∃ prior bound tail, prior+bound ≤ budget ∧
        DirectoryStageResult (R := R) (N := N) body program a (embStk placement (ordinaryOwnerBank metadata F))
          prior bound slot tail (fun j word => if LabelStock.live 64 (w+1) 1 j then ∀ x h,
            word (index ((projectorResidual finSumFinEquiv (reduce M proj) weights (fun i => Ring.inverse (weights i))
              (physicalLabel 64 (w+1) j)).mulVec x) h) = ownerRow rfl routed j (index x h)
            else ownerRow rfl routed j = word) finished) →
    let positive : 0 < columnCapacity := columnCapacity_pos
    let outer := fun f => statePlacedPr placement fits positive id (body f)
    ∃ z D n output, n ≤ stage.cost*(stage.tapes+5)+6+(1+budget) ∧
      Exec outer ((embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq
        (statePlacedNormalized placement fits positive id program)) (mk u (ordinaryOwnerBank metadata S)) n (mk z D) ∧
      z.user = u.user ∧ finished (embStk placement D) ∧
      RepT (stage.input (Function.update (stage.transform words) src output)) (embStk chart D).L (embStk chart D).R ∧
      PortReads R W parents interval weights routed output ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl output j = ownerRow rfl routed j := by
  intro M N proj stage src metadata words routed slot placement chart restore body program budget capacity chartFits fits u S finished input scanner positive outer
  let post := fun (out : Fin (R*N) → ZMod 2) (D : Stacks (T+5) prime) =>
    finished D ∧ PortReads R W parents interval weights routed out ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl out j = ownerRow rfl routed j
  obtain ⟨z,D,n,out,⟨done,reads,inactive⟩,time,run,user,ready,owners⟩ :=
    chartOwner_scan stage src metadata words restore positive body program budget post capacity chartFits fits u S input (by
      intro a F represented
      obtain ⟨prior,bound,tail,price,exec⟩ := scanner a F represented
      obtain ⟨y,B,t,out,user,time,run,reads,inactive,_,done⟩ := exec.portReads interval weights routed records upper
      exact ⟨y,B,prior+t,out,(Nat.add_le_add_left time prior).trans price,⟨done,reads,inactive⟩,user,run⟩)
  refine ⟨z,D,n,out,time,run,user,done,?_,reads,inactive⟩
  apply chartOwner_input stage _ (embStk chart D) _ ready _ (fun _ _ => ⟨rfl,rfl⟩)
  intro i j
  simpa [phaseOwners,embStk,chart] using (owners i j).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
