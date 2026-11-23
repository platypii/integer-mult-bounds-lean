module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartHost

/-! Charge the packed recursive calls once while executing a stage in flat parent order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine Certificates.PR589
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Tape setup and the two port corrections around a packed stage. -/
noncomputable def stageSetupCost [M8.Machine.Net] (base tapes V w : ℕ) : ℕ :=
  (base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5) +
    ((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*V+12

/-- A single coefficient pays the setup at every positive volume and width. -/
theorem stageSetupCost_bound [M8.Machine.Net] (base nt : ℕ) :
    ∃ D : ℝ, ∀ V w : ℕ, 0 < V → 0 < w →
      (stageSetupCost base nt V w : ℝ) ≤ D*V*(w : ℝ)^M8.Machine.BudgetBound.tau := by
  let setup := (RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152
  refine ⟨(base+17760*(2*|LeafCore.C|+14))*(nt+5)+setup+12,?_⟩
  intro V w vol hw
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have scaled : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have joins : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol) one
  have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right hw])
  have corr : ((base*V+17760*(2*LeafCore.coreCost V w+14) : ℕ) : ℝ) ≤
      (base+17760*(2*|LeafCore.C|+14))*(V*power) := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg base),core,joins]
  change (((base*V+17760*(2*LeafCore.coreCost V w+14))*(nt+5)+setup*V+12 : ℕ) : ℝ) ≤ _*V*power
  push_cast at corr ⊢
  nlinarith only [mul_le_mul_of_nonneg_right corr (show (0 : ℝ) ≤ nt+5 by positivity),joins,
    mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg setup)]

/-- The rounded sweep bill, including the fan handoff, has one uniform rate. -/
theorem sweepHandoffCost_bound [M8.Machine.Net] (base nt : ℕ) (rate : ℝ) :
    ∃ D : ℝ, ∀ V w : ℕ, 0 < V → 0 < w →
      let power := (w : ℝ)^M8.Machine.BudgetBound.tau
      ((⌊(stageSetupCost base nt V w : ℝ)+rate*V*power⌋₊+142081*(8*V+10)+1 : ℕ) : ℝ) ≤
        D*V*power := by
  obtain ⟨C,setup⟩ := stageSetupCost_bound base nt
  refine ⟨C+|rate|+142081*18+1,?_⟩
  intro V w vol hw power
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have scaled : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have unit : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol) one
  have rateBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self rate)
    (Nat.cast_nonneg V (α := ℝ))) (zero_le_one.trans one)
  have rounded := Nat.floor_le (show 0 ≤ (stageSetupCost base nt V w : ℝ)+ |rate| * V*power by positivity)
  have mono := Nat.floor_mono (add_le_add (le_refl (stageSetupCost base nt V w : ℝ)) rateBound)
  have bill : (⌊(stageSetupCost base nt V w : ℝ)+rate*V*power⌋₊ : ℝ) ≤
      (stageSetupCost base nt V w : ℝ)+ |rate| * V*power := (Nat.cast_le.mpr mono).trans rounded
  push_cast
  have setupBound : (stageSetupCost base nt V w : ℝ) ≤ C*V*power := setup V w vol hw
  linarith only [bill,setupBound,scaled,unit]

theorem packedFlatStage_cost [M8.Machine.Net] :
    ∃ (C : ℝ) (base nt states : ℕ), ∀ {Q h B rows : ℕ} {P U : Type}
    (node : RecursiveInterchangeLayout.Descriptor) (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop)
    (_capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (_width : node.width = 64*(h+1)) (_split : node.rows = 142080*rows)
    (_label : node.beforeH = B*prime^(64*((h+1)*64))),
    let w := h+1
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let M := prime^w
    let W := B*prime^(64*(w*64))*K
    let V := M^16*(M^112*B*prime^(64*(w*64))*K)
    let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [V,W,Nat.mul_assoc])
    states ≤ Q → 0 < B → 0 < K → role.Positive →
    PackedStageExecution (w := w) (B := B) (K := K) n tapes body coeff required →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (tapes p) ↪ Fin T),
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
    let full := (fan.trans owner).trans stage
    let worker := fun f : (_ : StageRun) × P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg stage id (embProg owner id (worker f))
    ∀ childTime, required childTime →
    let children := ((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum
    ∃ (t₁ t₂ : ℕ) (mid : Fin (80+((T+273)+LeafCore.small)) ↪ Fin t₁)
      (outer : Fin t₁ ↪ Fin t₂) (code : Pr ((_ : StageRun) × P) t₂ Q prime U),
      let live := (full.trans mid).trans outer
      ∃ seed : Stacks t₂ prime, ∀ x u S, HelperFan live x S →
        (∀ j, (∀ i, live i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z F k y, Exec (fun f => embProg outer id (embProg mid id (host f))) code (mk u S) k (mk z F) ∧
          (k : ℝ) ≤ (stageSetupCost base nt V w : ℝ) +
            (C+|stagePackingRate n+(stageRuns.map coeff).sum|)*V*(w : ℝ)^M8.Machine.BudgetBound.tau+children ∧
          z.user = u.user ∧ HelperFan live y F ∧ ∀ j : Fin W,
            let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
            readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,base,nt,states,chart⟩ := borrowedFlatChart_exec
  let setup := (RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152
  refine ⟨C,base,nt,states,?_⟩
  intro Q h B rows P U node n tapes body coeff required capacity width split label w role K M W V size fits hB hK pos packed
  obtain ⟨T,fan,bank,build⟩ := parentPackedStage_exec node n tapes body coeff required capacity width split label pos packed
  refine ⟨T,fan,bank,?_⟩
  intro stage owner full worker host time ready children
  obtain ⟨initial,program,run⟩ := build time ready
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  let rate := stagePackingRate n+(stageRuns.map coeff).sum
  let cap : ℝ := (setup*V : ℕ) + |rate| *(V*power)
  let price := ⌊cap⌋₊ + children
  have hw : 1 ≤ w := Nat.succ_pos h
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have hp := Shared50ModularControl.prime_prime.pos
  have vol : 0 < V := by dsimp [V,M]; positivity
  have joins : 1 ≤ (V : ℝ)*power := one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol) one
  have nonneg : 0 ≤ cap := by dsimp [cap]; positivity
  have raw := chart n full host program price initial hw hB hK fits (by
    intro x u S live fresh
    obtain ⟨z,F,t,y,exec,paid,user,out,action⟩ := run x u S live fresh
    refine ⟨z,F,t,y,exec,?_,user,out,action⟩
    have bound : (t : ℝ) ≤ cap+children := by
      change (t : ℝ) ≤ ((setup*V : ℕ) : ℝ)+(rate*(V*power)+children) at paid
      dsimp only [cap]
      linarith only [paid,
        mul_le_mul_of_nonneg_right (le_abs_self rate) (le_trans zero_le_one joins)]
    have := Nat.le_floor bound
    simpa only [price,Nat.floor_add_natCast nonneg] using this)
  obtain ⟨t₁,t₂,mid,outer,code,prepare⟩ := raw
  obtain ⟨seed,_,execute⟩ := prepare ⟨[],[],fun _ => [],fun _ => []⟩
  refine ⟨t₁,t₂,mid,outer,code,seed,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,k,y,exec,paid,user,out,action⟩ := execute x u S live fresh
  refine ⟨z,F,k,y,exec,?_,user,out,action⟩
  change (k : ℝ) ≤ (((base*V+17760*(2*LeafCore.coreCost V w+14))*(nt+5)+price+12 : ℕ) : ℝ)+C*V*power at paid
  dsimp only [price,cap] at paid
  change (k : ℝ) ≤ (((base*V+17760*(2*LeafCore.coreCost V w+14))*(nt+5)+setup*V+12 : ℕ) : ℝ)+
    (C+|rate|)*V*power+children
  have floorBound := Nat.floor_le nonneg
  dsimp only [cap] at floorBound
  push_cast at paid floorBound ⊢
  linarith only [paid,floorBound]

theorem packedFlatStage_exec [M8.Machine.Net] :
    ∃ (C : ℝ) (states : ℕ), ∀ {Q h B rows : ℕ} {P U : Type}
    (node : RecursiveInterchangeLayout.Descriptor) (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop)
    (_capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (_width : node.width = 64*(h+1)) (_split : node.rows = 142080*rows)
    (_label : node.beforeH = B*prime^(64*((h+1)*64))),
    let w := h+1
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let M := prime^w
    let W := B*prime^(64*(w*64))*K
    let V := M^16*(M^112*B*prime^(64*(w*64))*K)
    let size : M^128*W = V := (ordinaryCompact_width M W).symm.trans (by simp [V,W,Nat.mul_assoc])
    states ≤ Q → 0 < B → 0 < K → role.Positive →
    PackedStageExecution (w := w) (B := B) (K := K) n tapes body coeff required →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (tapes p) ↪ Fin T),
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
    let full := (fan.trans owner).trans stage
    let worker := fun f : (_ : StageRun) × P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg stage id (embProg owner id (worker f))
    ∀ childTime, required childTime →
    let children := ((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum
    ∃ (t₁ t₂ : ℕ) (mid : Fin (80+((T+273)+LeafCore.small)) ↪ Fin t₁)
      (outer : Fin t₁ ↪ Fin t₂) (code : Pr ((_ : StageRun) × P) t₂ Q prime U),
      let live := (full.trans mid).trans outer
      ∃ seed : Stacks t₂ prime, ∀ x u S, HelperFan live x S →
        (∀ j, (∀ i, live i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z F k y, Exec (fun f => embProg outer id (embProg mid id (host f))) code (mk u S) k (mk z F) ∧
          (k : ℝ) ≤ (C+|stagePackingRate n+(stageRuns.map coeff).sum|)*V*(w : ℝ)^M8.Machine.BudgetBound.tau+children ∧
          z.user = u.user ∧ HelperFan live y F ∧ ∀ j : Fin W,
            let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
            readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨C,base,nt,states,execute⟩ := packedFlatStage_cost
  obtain ⟨D,setup⟩ := stageSetupCost_bound base nt
  refine ⟨C+D,states,?_⟩
  intro Q h B rows P U node n tapes body coeff required capacity width split label w role K M W V size fits hB hK pos packed
  obtain ⟨T,fan,bank,build⟩ := execute node n tapes body coeff required capacity width split label fits hB hK pos packed
  refine ⟨T,fan,bank,?_⟩
  intro stage owner full worker host time ready children
  obtain ⟨t₁,t₂,mid,outer,code,seed,run⟩ := build time ready
  refine ⟨t₁,t₂,mid,outer,code,seed,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,k,y,exec,paid,user,out,action⟩ := run x u S live fresh
  refine ⟨z,F,k,y,exec,?_,user,out,action⟩
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  let rate := stagePackingRate n+(stageRuns.map coeff).sum
  have hw : 1 ≤ w := Nat.succ_pos h
  have hp := Shared50ModularControl.prime_prime.pos
  have vol : 0 < V := by dsimp [V,M]; positivity
  change (k : ℝ) ≤ (stageSetupCost base nt V w : ℝ)+(C+|rate|)*V*power+children at paid
  change (k : ℝ) ≤ (C+D+|rate|)*V*power+children
  have bound : (stageSetupCost base nt V w : ℝ) ≤ D*V*power := setup V w vol hw
  linarith only [paid,bound]

end IntegerMultBounds.MathlibTM2.M6.BitNode
