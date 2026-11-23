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

noncomputable def returnedFan {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) :
    Fin (142081+2) ↪ Fin (Exit.size 0 T) :=
  finSumFinEquiv.symm.toEmbedding.trans (Exit.place
    (Sum.elim (fun i => Exit.Register.sweep (owners i))
      (fun j : Fin 2 => Exit.Register.chart (fan (j.natAdd 142081))))
    (by rintro (i|i) (j|j) eq <;> simp_all [owners.injective.eq_iff,fan.injective.eq_iff]
        exact (Fin.natAddEmb 142081).injective eq))

theorem returnedFan_owner {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (i : Fin 142081) : returnedFan fan (i.castAdd 2) = Exit.sweep 0 T (owners i) := by
    change (Fintype.equivFin _) (Sum.elim _ _ (finSumFinEquiv.symm (i.castAdd 2))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl

theorem returnedFan_counter {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (j : Fin 2) : returnedFan fan (j.natAdd 142081) = Exit.chart 0 T (fan (j.natAdd 142081)) := by
    change (Fintype.equivFin _) (Sum.elim _ _ (finSumFinEquiv.symm (j.natAdd 142081))) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- A physical piece acts on exact parent words with a prepared private workspace. -/
def PackedPieceHandoff {P U : Type} {t q : ℕ} (V : ℕ)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (body : P → Pr P t q prime U) (code : Pr P t q prime U)
    (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) (price : ℕ) : Prop :=
  ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x S →
    (∀ j, (∀ i, src i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F steps y, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ price ∧ z.user = u.user ∧
      ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ effect x y

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
    let host := fun f => embProg place id (embProg worker id (host f))
    let labels := prime^(64*((h+1)*64))
    let W := B*labels*K
    let bill := (base*V+17760*(2*M8.RevMachine.LeafCore.coreCost V (h+1)+14))*(correctionTapes+5)+price+12
    ∃ code C, ∀ H (parent : Fin 64 → ZMod M) (units : ∀ i, IsUnit (parent i)),
    M^128 < 2^H → H ≤ M^128+1 → 0 < W → ∃ prepared : Stacks (Exit.size 0 N) prime,
      ((∑ j, (8*(prepared.R (Exit.sweep 0 N (work (returnSeedSlots j)))).length+6))+1 ≤ 625*(M^128*W)) ∧
      PackedPieceHandoff (M^16*(1*(M^112*W))) (borrowedStageHandoff (h+1) B K parent units n)
        host code fan (returnedFan (full.trans worker)) prepared
        (bill + (142081*(8*V+10)+1) + (142080*(C*(M^16*(labels*(M^112*W)))+16)+2)) := by
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
  let W := B*prime^(64*((h+1)*64))*K
  let prepared := packedStageStacks seed h H W parent
  have placed := packedStageSeed (full.trans inner) seed h H W parent
  refine ⟨prepared,packedStageStacks_returnCost seed h H W parent widthPos bits,?_⟩
  intro x u S words fresh
  obtain ⟨headers,privateTapes,tmpL,tmpR,empty⟩ := placed S fresh
  have spare := words.right (Fin.last 142080)
  obtain ⟨z,G,k,d,done,bound,same,handoff,controls,left,last,roles⟩ :=
    execute H parent units height bits widthPos x u S headers (fun r => words.left _) (fun r => words.right _)
      (by intro j; rw [words.left _,spare,readAt_nil_left,putWord_blank_zero]) (borrowedOwnerVolume (h+1) B K ▸ words.controls) privateTapes
      tmpL tmpR (fun i => (empty i).2)
  refine ⟨z,G,k,d,done,bound,same,⟨?_,?_,?_⟩,handoff⟩
  · intro i
    rw [returnedFan_owner]
    exact (left i).trans (empty i).1
  · intro i
    rw [returnedFan_owner]
    induction i using Fin.lastCases with
    | last => exact last
    | cast i =>
      obtain ⟨r,rfl⟩ := ((Fintype.equivFin Role).trans (finCongr card_role)).surjective i
      exact roles r
  · intro j z
    rw [returnedFan_counter,borrowedOwnerVolume (h+1) B K]
    exact controls j z

end IntegerMultBounds.MathlibTM2.M6.BitNode
