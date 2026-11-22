module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageEntry

/-! Execute the packed PR589 stage from physical parent-order owner words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile SweepFile.Exit
open M8.RevMachine Certificates.PR589
open Shared50ModularControl (prime)

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
    let tmp := Exit.tmp 0 N
    let host := fun f => embProg place id (embProg worker id (host f))
    let labels := prime^(64*((h+1)*64))
    let W := B*labels*K
    let bill := (base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V (h+1)+14))*(correctionTapes+5)+price+12
    ∃ code C, ∃ seed : Stacks N prime, ∀ H (parent : Fin 64 → ZMod M) (units : ∀ i, IsUnit (parent i)),
    M^128 < 2^H → H ≤ M^128+1 → 0 < W →
    ∀ (x : OwnerArray (h+1) 1 W) (u : HS (Exit.size 0 N) Q prime U) (S : Stacks (Exit.size 0 N) prime),
    ReturnHeaders h H parent W 1 (embStk back S).R →
    (∀ r, S.L (fan ((sweepRoleTape r).castAdd 2)) = []) →
    (∀ r, S.R (fan ((sweepRoleTape r).castAdd 2)) = List.ofFn fun j => SparseRoleCircuit.encode (x (sweepRoleTape r) j)) →
    WordAtZero (x (Fin.last 142080)) (S.L (fan ((Fin.last 142080).castAdd 2))) (S.R (fan ((Fin.last 142080).castAdd 2))) →
    StageControls fan V S →
    (∀ j, (∀ i, (full.trans worker) i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
    S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (back (owners i)) = []) →
    ∃ (z : HS (Exit.size 0 N) Q prime U) (G : Stacks (Exit.size 0 N) prime) (k : ℕ) (d : OwnerArray (h+1) 1 W), Exec host code (mk u S) k (mk z G) ∧
      k ≤ bill + (142081*(8*V+10)+1) + (142080*(C*(M^16*(labels*(M^112*W)))+16)+2) ∧
      z.user = u.user ∧ borrowedStageHandoff (h+1) B K parent units n x d ∧
      (∀ i, G.L (back (owners i)) = S.L (back (owners i))) ∧
      G.R (back (owners (Fin.last 142080))) = List.ofFn (fun j => SparseRoleCircuit.encode (d (Fin.last 142080) j)) ∧
      ∀ r, G.R (back (owners (sweepRoleTape r))) = List.ofFn fun j => SparseRoleCircuit.encode (d (sweepRoleTape r) j) := by
  obtain ⟨base,correctionTapes,states,physical⟩ := correctedPhysicalStage_exec
  refine ⟨base,correctionTapes,states,?_⟩
  intro Q h B rows P U node n tapes body coeff required capacity width split label role K M V fits positive pos packed
  obtain ⟨T,fan,bank,build⟩ := parentPackedStage_exec node n tapes body coeff required capacity width split label pos packed
  refine ⟨T,fan,bank,?_⟩
  intro stage owner full worker host time ready price
  obtain ⟨initial,program,run⟩ := build time ready
  apply physical n full host program price initial positive fits
  intro x u S live fresh
  obtain ⟨z,F,t,y,exec,paid,user,out,action⟩ := run x u S live fresh
  exact ⟨z,F,t,y,exec,Nat.cast_le.mp (paid.trans (Nat.le_ceil _)),user,out,action⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
