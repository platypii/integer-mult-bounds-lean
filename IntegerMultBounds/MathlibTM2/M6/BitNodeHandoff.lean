module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeBridgeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitNodeExchangeHandoff

/-! Assemble PR589 from its nine sweeps and nine nonterminal remainders. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

def nodePieceEffect (w B tail : ℕ)
    (idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop)
    (stage : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop) :
    Piece → OwnerArray w B tail → OwnerArray w B tail → Prop
  | .stage i => stage i
  | .remainder i => if h : i < 9 then idle ⟨i,h⟩ else fun x y => y = x
  | .bridge d s => fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j
  | .exchangeSides => fun x y => y = x ∘ exchangeOwner

abbrev nodeHandoffEffect (w B tail : ℕ) (idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop) :=
  nodePieceEffect w B tail idle (fun i => sweepEffect i w B tail)

open Certificates.PR589.Nine in
/-- Reading the physical handoff trace in execution order yields the logical
node action whenever its sweeps and remainders realize their role reads. -/
theorem nodePieceEffect_read {w B tail : ℕ}
    {stage idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop}
    (address : (Axis ⊕ Axis → ℚ) → Fin ((prime^w)^16*(B*((prime^w)^112*tail))))
    (sweep : ∀ i x y, stage i x y →
      readRoles address y = (Piece.stage i).run (readRoles address x))
    (rest : ∀ i x y, idle i x y →
      readRoles address y = (Piece.remainder i.val).run (readRoles address x))
    {x y} (trace : nodeProgram.foldr
      (fun p cont a => ∃ b, nodePieceEffect w B tail idle stage p a b ∧ cont b)
      (fun a => a = y) x) : readRoles address y = runNode (readRoles address x) := by
  have piece (p : Piece) (hp : p ∈ nodeProgram) (a b) (step : nodePieceEffect w B tail idle stage p a b) :
      readRoles address b = p.run (readRoles address a) := by
    cases p with
    | stage i => exact sweep i a b step
    | remainder i =>
      by_cases hi : i < 9
      · exact rest ⟨i,hi⟩ a b (by simpa [nodePieceEffect,hi] using step)
      · have last : i = 9 := by simp [nodeProgram] at hp; omega
        subst i
        simpa [nodePieceEffect,terminalIdle_run] using congrArg (readRoles address)
          (show b = a from step)
    | exchangeSides =>
      subst b
      funext r z
      exact congrArg (fun j => a j (address z)) (exchangeOwner_role r)
    | bridge d s =>
      subst b
      funext r z
      let index := (Fintype.equivFin Role).trans (finCongr card_role)
      change bridgeColumn d s (fun j => a j (address z)) (index r).castSucc = _
      simp only [bridgeColumn,Fin.lastCases_castSucc,show ((Fintype.equivFin Role).trans
        (finCongr card_role)).symm (index r) = r from index.symm_apply_apply r,Piece.run]
      split <;> first | rfl | split <;> rfl
  have go (ps : List Piece) (inside : ∀ p ∈ ps, p ∈ nodeProgram) (a)
      (h : ps.foldr (fun p cont x => ∃ b, nodePieceEffect w B tail idle stage p x b ∧ cont b)
        (fun x => x = y) a) : readRoles address y = runPieces ps (readRoles address a) := by
    induction ps generalizing a with
    | nil => exact congrArg (readRoles address) h.symm
    | cons p ps ih =>
      obtain ⟨b,step,h⟩ := h
      change readRoles address y = runPieces ps (p.run (readRoles address a))
      rw [← piece p (inside p List.mem_cons_self) a b step]
      exact ih (fun j hj => inside j (List.mem_cons_of_mem _ hj)) b h
  exact go nodeProgram (fun _ h => h) x trace

open Certificates.PR589.Nine in
theorem nodeHandoffEffect_read {w B tail : ℕ}
    {idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop}
    (address : (Axis ⊕ Axis → ℚ) → Fin ((prime^w)^16*(B*((prime^w)^112*tail))))
    (sweep : ∀ i x y, sweepEffect i w B tail x y →
      readRoles address y = (Piece.stage i).run (readRoles address x))
    (rest : ∀ i x y, idle i x y →
      readRoles address y = (Piece.remainder i.val).run (readRoles address x))
    {x y} (trace : nodeProgram.foldr
      (fun p cont a => ∃ b, nodeHandoffEffect w B tail idle p a b ∧ cont b)
      (fun a => a = y) x) : readRoles address y = runNode (readRoles address x) :=
  nodePieceEffect_read address sweep rest trace

def nodeHandoffCost (V : ℕ) (sweep idle : Fin 9 → ℕ) : Piece → ℕ
  | .stage i => sweep i
  | .remainder i => if h : i < 9 then idle ⟨i,h⟩ else 1
  | .bridge .. => 2*(76*17760*V*(142081+7)+6)+1
  | .exchangeSides => 1

/-- Nine sweep and remainder budgets, nine directed bridges, and two
one-step terminal instructions account for the complete schedule. -/
theorem nodeHandoffCost_sum (V : ℕ) (sweep idle : Fin 9 → ℕ) :
    (nodeProgram.map (nodeHandoffCost V sweep idle)).sum =
      (∑ i, sweep i) + (∑ i, idle i) + 9*(2*(76*17760*V*(142081+7)+6)+1)+2 := by
  let ns := List.finRange 9
  have perm : nodeProgram.Perm (ns.map Piece.stage ++ ns.map (fun i => Piece.remainder i.val) ++
      bridgeEdges.map (fun p => Piece.bridge p.1 p.2) ++ [.remainder 9,.exchangeSides]) := by decide +kernel
  rw [(perm.map _).sum_eq]
  have ranks (f : Fin 9 → ℕ) : (ns.map f).sum = ∑ i, f i := by
    simpa only [ns,List.ofFn_eq_map] using (List.sum_ofFn : (List.ofFn f).sum = _)
  have lengthBridges : bridgeEdges.length = 9 := by decide
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,nodeHandoffCost,dite_eq_left (Fin.isLt _),Fin.eta,
    dite_eq_right (by decide : ¬9 < 9),ranks,List.map_const',List.sum_replicate,lengthBridges,nsmul_eq_mul]
  omega

private noncomputable def bridgeStates : Piece → ℕ
  | .bridge d s => if h : Piece.bridge d s ∈ nodeProgram then (bridgeHandoff d s h).choose else 0
  | _ => 0

/-- All nonrecursive pieces are supplied at one common state capacity. -/
theorem assembledPieceHandoff {U : Type} :
    ∃ states : ℕ, ∀ {q : ℕ}, states ≤ q → ∀ w B tail : ℕ,
    let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*tail))
    0 < V → ∀ (stage idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop)
      (sweepCost idleCost : Fin 9 → ℕ),
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (stage i) body code src dst prepared (sweepCost i)) →
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (idle i) body code src dst prepared (idleCost i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (fun x y => nodeProgram.foldr
        (fun i cont a => ∃ b, nodePieceEffect w B tail idle stage i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared
        ((∑ i, sweepCost i) + (∑ i, idleCost i) + 9*(2*(76*17760*V*(142081+7)+6)+1)+2) := by
  refine ⟨(nodeProgram.map bridgeStates).sum,?_⟩
  intro q fits w B tail V pos stage idle sweepCost idleCost sweep remainder
  rw [← nodeHandoffCost_sum]
  apply nodeHandoffs
  intro piece mem
  let fan := Function.Embedding.refl (Fin (142081+2))
  let prepared : Stacks (142081+2) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  let body : Empty → Pr Empty (142081+2) q prime U := Empty.elim
  cases piece with
  | stage i =>
    obtain ⟨P,t,b,c,src,dst,L,run⟩ := sweep i
    exact ⟨P,t,b,c,src,dst,L,run⟩
  | remainder i =>
    by_cases h : i < 9
    · simpa only [nodePieceEffect,nodeHandoffCost,dite_eq_left h] using remainder ⟨i,h⟩
    · refine ⟨Empty,_,body,.act .done,fan,fan,prepared,?_⟩
      simp only [nodePieceEffect,nodeHandoffCost,dite_eq_right h]
      intro x u S live _
      exact ⟨u,S,1,x,Exec.act _ _,le_rfl,rfl,live,rfl⟩
  | bridge d s =>
    have cap := (List.le_sum_of_mem (List.mem_map_of_mem (f := bridgeStates) mem)).trans fits
    simp only [bridgeStates,dite_eq_left mem] at cap
    obtain ⟨c,run⟩ := (bridgeHandoff d s mem).choose_spec fan body cap
    exact ⟨Empty,_,body,c,fan,fan,prepared,run w B tail pos prepared⟩
  | exchangeSides =>
    obtain ⟨c,dst,run⟩ := exchangeSidesHandoff w B tail body fan prepared
    exact ⟨Empty,_,body,c,fan,dst,prepared,run⟩

theorem assembledNodeHandoff {U : Type} :
    ∃ states : ℕ, ∀ {q : ℕ}, states ≤ q → ∀ w B tail : ℕ,
    let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*tail))
    0 < V → ∀ (idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop)
      (sweepCost idleCost : Fin 9 → ℕ),
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      StageHandoffExec i w B tail body code src dst prepared (sweepCost i)) →
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (idle i) body code src dst prepared (idleCost i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (fun x y => nodeProgram.foldr
        (fun i cont a => ∃ b, nodeHandoffEffect w B tail idle i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared
        ((∑ i, sweepCost i) + (∑ i, idleCost i) + 9*(2*(76*17760*V*(142081+7)+6)+1)+2) := by
  obtain ⟨states,assemble⟩ := assembledPieceHandoff (U := U)
  refine ⟨states,?_⟩
  intro q fits w B tail V pos idle sweepCost idleCost sweep remainder
  apply assemble fits w B tail pos _ idle sweepCost idleCost _ remainder
  intro i
  obtain ⟨P,t,b,c,src,dst,L,run⟩ := sweep i
  exact ⟨P,t,b,c,src,dst,L,run.toPiece⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
