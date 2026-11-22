module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageEntry
public import IntegerMultBounds.MathlibTM2.M6.BitPackedReturnHeaders

/-! Execute the packed PR589 stage from physical parent-order owner words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile SweepFile.Exit
open M8.RevMachine Certificates.PR589
open Shared50ModularControl (prime)

/-- Physical inputs shared across stage boundaries. The owner words begin
at their left ends and the two controls describe their common volume. -/
structure ParentStageWords {T N : ℕ} (port : Fin 142081 → Fin T)
    (fan : Fin (142081+2) ↪ Fin T) (V : ℕ) (x : Fin 142081 → Fin N → ZMod 2)
    (S : Stacks T prime) : Prop where
  left : ∀ i, S.L (port i) = []
  right : ∀ i, S.R (port i) = List.ofFn fun j => SparseRoleCircuit.encode (x i j)
  controls : StageControls fan V S

/-- Read a preceding stage's output as the next embedded stage's input
when its owner and counter ports occupy the same host tapes. -/
theorem ParentStageWords.next {T A N V : ℕ} {port : Fin 142081 → Fin T}
    {fan : Fin (142081+2) ↪ Fin T} {x : Fin 142081 → Fin N → ZMod 2} {S : Stacks T prime}
    (words : ParentStageWords port fan V x S) (place : Fin A ↪ Fin T) (nextFan : Fin (142081+2) ↪ Fin A)
    (owners : ∀ i, place (nextFan (i.castAdd 2)) = port i)
    (counters : ∀ j : Fin 2, place (nextFan (j.natAdd 142081)) = fan (j.natAdd 142081)) :
    ParentStageWords (fun i => nextFan (i.castAdd 2)) nextFan V x (embStk place S) := by
  constructor
  · intro i
    exact (congrArg S.L (owners i)).trans (words.left i)
  · intro i
    exact (congrArg S.R (owners i)).trans (words.right i)
  · intro j z
    simpa only [embStk,Function.comp_apply,counters] using words.controls j z

/-- Execute the packed invocation family, corrections, and both owner permutations
with the recursive child bill charged once. -/
theorem packedPhysicalStage_exec [M8.Machine.Net] :
    ∃ base correctionTapes states : ℕ, ∀ {Q h B rows : ℕ} {P U : Type}
    (node : RecursiveInterchangeLayout.Descriptor) (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop)
    (_capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (_width : node.width = 64*(h+1)) (_split : node.rows = 142080*rows)
    (_label : node.beforeH = B*prime^(64*((h+1)*64))),
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let M := prime^(h+1)
    let V := M^16*((M^112*B)*prime^(64*((h+1)*64))*K)
    states ≤ Q → 0 < (M^112*B)*prime^(64*((h+1)*64))*K → role.Positive → PackedStageExecution (w := h+1) (B := B) (K := K) n tapes body coeff required →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (tapes p) ↪ Fin T),
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
    let full := (fan.trans owner).trans stage
    let worker := fun f : (_ : StageRun) × P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg stage id (embProg owner id (worker f))
    ∀ childTime, required childTime →
    let price := ⌈((((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*V : ℕ)+
          ((stagePackingRate n+(stageRuns.map coeff).sum)*(V*((h+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Certificates.PR589.Geometry.Moves.localPaid)).length).map childTime).sum) : ℝ)⌉₊
    ∃ (N : ℕ) (worker : Fin (80+((T+273)+LeafCore.small)) ↪ Fin N),
    let place := Exit.chart 0 N
    let fan := (full.trans worker).trans place
    let back := Exit.sweep 0 N
    let host := fun f => embProg place id (embProg worker id (host f))
    let labels := prime^(64*((h+1)*64))
    let W := B*labels*K
    let bill := (base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V (h+1)+14))*(correctionTapes+5)+price+12
    ∃ code C, ∀ H (parent : Fin 64 → ZMod M) (units : ∀ i, IsUnit (parent i)),
    M^128 < 2^H → H ≤ M^128+1 → 0 < W → ∃ prepared : Stacks (Exit.size 0 N) prime,
    ∀ (x : OwnerArray (h+1) 1 W) (u : HS (Exit.size 0 N) Q prime U) (S : Stacks (Exit.size 0 N) prime),
    ParentStageWords (fun i => fan (i.castAdd 2)) fan V x S →
    (∀ j, (∀ i, fan i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ (z : HS (Exit.size 0 N) Q prime U) (G : Stacks (Exit.size 0 N) prime) (k : ℕ) (d : OwnerArray (h+1) 1 W), Exec host code (mk u S) k (mk z G) ∧
      k ≤ bill + (142081*(8*V+10)+1) + (142080*(C*(M^16*(labels*(M^112*W)))+16)+2) ∧
      z.user = u.user ∧ borrowedStageHandoff (h+1) B K parent units n x d ∧
      ParentStageWords (fun i => back (owners i)) fan V d G := by
  obtain ⟨base,correctionTapes,states,physical⟩ := correctedPhysicalStage_exec
  refine ⟨base,correctionTapes,states,?_⟩
  intro Q h B rows P U node n tapes body coeff required capacity width split label role K M V fits positive pos packed
  obtain ⟨T,fan,bank,build⟩ := parentPackedStage_exec node n tapes body coeff required capacity width split label pos packed
  refine ⟨T,fan,bank,?_⟩
  intro stage owner full worker host time ready price
  obtain ⟨initial,program,run⟩ := build time ready
  have sweep := physical n full host program price initial positive fits (by
    intro x u S live fresh
    obtain ⟨z,F,t,y,exec,paid,user,out,action⟩ := run x u S live fresh
    exact ⟨z,F,t,y,exec,Nat.cast_le.mp (paid.trans (Nat.le_ceil _)),user,out,action⟩)
  obtain ⟨N,inner,code,C,seed,execute⟩ := sweep
  refine ⟨N,inner,code,C,?_⟩
  intro H parent units height bits widthPos
  obtain ⟨prepared,placed⟩ := packedStageSeed (full.trans inner) seed h H _ parent
  refine ⟨prepared,?_⟩
  intro x u S words fresh
  obtain ⟨headers,privateTapes,tmpL,tmpR,empty⟩ := placed S fresh
  have spare := words.right (Fin.last 142080)
  obtain ⟨z,G,k,d,done,bound,same,handoff,controls,left,last,roles⟩ :=
    execute H parent units height bits widthPos x u S headers (fun r => words.left _) (fun r => words.right _)
      (by intro j; rw [words.left _,spare,readAt_nil_left,putWord_blank_zero]) words.controls privateTapes
      tmpL tmpR (fun i => (empty i).2)
  refine ⟨z,G,k,d,done,bound,same,handoff,fun i => (left i).trans (empty i).1,?_,controls⟩
  intro i
  induction i using Fin.lastCases with
  | last => exact last
  | cast i =>
    obtain ⟨r,rfl⟩ := ((Fintype.equivFin Role).trans (finCongr card_role)).surjective i
    exact roles r

end IntegerMultBounds.MathlibTM2.M6.BitNode
