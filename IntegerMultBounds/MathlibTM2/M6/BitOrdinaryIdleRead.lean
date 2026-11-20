module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interpret the ordinary PR589 owner tapes at a common live label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout

open Stack Host

/-- Place each local owner program on the same permanent owners and a
disjoint private bank, even when its local owner slots are scattered. -/
noncomputable def idlePassBank {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) :=
  (returnChartBank slots (Function.Embedding.refl _)).trans (Fallback.Record.exchangeBank owners width k)

theorem idlePassBank_owner {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) (i : Fin owners) :
    idlePassBank width k slots (slots i) = i.castAdd _ := by
  unfold idlePassBank
  rw [Function.Embedding.trans_apply,returnChartBank_selected,Fallback.Record.exchangeBank_shared]
  rfl

/-- Install each owner's procedure under its occurrence index. Local recursive
calls stay in that owner's procedure table and use its private tapes. -/
noncomputable def idlePassBody {owners n Q : ℕ} {P U : Type} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (body : ∀ k, P → Pr P (width k) Q prime U)
    (f : Fin n × P) : Pr (Fin n × P) (owners + Fintype.card (Σ j, Fin (width j))) Q prime U :=
  embProg (idlePassBank width f.1 (slots f.1)) (Prod.mk f.1) (body f.1 f.2)

/-- Embedding an execution preserves the exact time and both stacks of every
other pass's private tapes, including its preloaded scanner metadata. -/
theorem idlePassBank_exec {owners n Q : ℕ} {P U : Type} (width : Fin n → ℕ) (k : Fin n)
    (slots : ∀ j, Fin owners ↪ Fin (width j)) (body : ∀ j, P → Pr P (width j) Q prime U)
    (p : Pr P (width k) Q prime U) (v : HS _ Q prime U) (S : Stacks _ prime)
    (z : HS (width k) Q prime U) (D : Stacks (width k) prime) (t : ℕ)
    (run : Exec (body k) p (mk (embDn (idlePassBank width k (slots k)) v) (embStk (idlePassBank width k (slots k)) S)) t (mk z D)) :
    ∃ u F, Exec (idlePassBody width slots body) (embProg (idlePassBank width k (slots k)) (Prod.mk k) p) (mk v S) t (mk u F) ∧
      u.user = z.user ∧ embStk (idlePassBank width k (slots k)) F = D ∧
      ∀ j, j ≠ k → ∀ a : Fin (width j),
        let h := Fin.natAdd owners (Fallback.Record.exchangeScratch width j a)
        F.L h = S.L h ∧ F.R h = S.R h := by
  obtain ⟨u,F,exec,_,user,view,kept⟩ := exec_emb (idlePassBank width k (slots k)).injective (body' := idlePassBody width slots body) (ι := Prod.mk k) (fun _ => rfl) run v rfl S rfl
  refine ⟨u,F,exec,user,view,fun j ne a => kept _ (fun b => ?_)⟩
  exact Fallback.Record.exchangeBank_avoids owners width (Ne.symm ne) _ a

/-- Sequence the physical passes on the idle's distinct owners. Each pass may
return a different representation of the tape bank and has its own time bound. -/
theorem idleCopies_exec {T Q : ℕ} {P U α : Type} (i : Fin 9)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → α) → Stacks T prime → Prop)
    (effect : (Fin 32 × Fin 5) × Fin 222 → α → α → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        effect k (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  have run (ks : List ((Fin 32 × Fin 5) × Fin 222)) (distinct : ks.Nodup)
      (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k ∈ ks, prepared k S) :
      ∃ y D z n, Exec body (Prog.seqList (ks.map program)) (mk u S) n (mk z D) ∧
        (n : ℝ) ≤ (ks.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
        (∀ k ∈ ks, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k ∈ ks, j ≠ idleTape i k) → y j = x j := by
    induction ks generalizing x S u with
    | nil =>
      exact ⟨x,S,u,1,Exec.act .done _,by simp,rfl,input,by simp,fun _ _ => rfl⟩
    | cons k ks ih =>
      obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
      obtain ⟨v,B,t,m,firstRun,paid,keep,next,preserve,acted,off⟩ := pass k x S u input (frames k List.mem_cons_self)
      obtain ⟨y,D,z,n,rest,bill,user,final,acts,kept⟩ := ih tail v B t next
        (fun a ha => preserve a (fun h => fresh (h ▸ ha)) (frames a (List.mem_cons_of_mem _ ha)))
      refine ⟨y,D,z,m+n,Exec.seq firstRun rest,?_,user.trans keep,final,?_,?_⟩
      · simp only [List.map_cons,List.sum_cons,Nat.cast_add]
        linarith
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | member
        · rw [kept (idleTape i j) (fun a ha => (idleTape_injective i).ne (fun h => fresh (h.symm ▸ ha)))]
          exact acted
        · rw [← off _ ((idleTape_injective i).ne (fun h => fresh (h ▸ member)))]
          exact acts j member
      · intro j outside
        exact (kept j (fun a ha => outside a (List.mem_cons_of_mem _ ha))).trans
          (off j (outside k List.mem_cons_self))
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := run idleCopies
    (stageRuns_nodup.product (List.nodup_finRange _)) x S u input (fun k _ => frames k)
  refine ⟨y,D,z,n,exec,paid,user,final,fun k => acts k ?_,fun j h => kept j (fun a _ => h a)⟩
  exact List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩

/-- Physical cell of a rational address in the fixed block, label and spectator slice. -/
noncomputable def ordinaryRoleAddress {w R W parents : ℕ} (parent : Fin 64 → ZMod (prime^(w+1)))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1))
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W) :
    (Axis ⊕ Axis → ℚ) → Fin (R*((prime^(w+1))^128*W)) :=
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let pack := fun x => finProdFinEquiv (row,index ((frame.mulVec (x ∘ axes)) ∘ finSumFinEquiv.symm) spectator)
    pack ∘ addressMod M

/-- All selected owners realize the compiled idle at the same packed address
for each live label, inherited block and spectator. -/
theorem ordinaryIdle_read {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let address := ordinaryRoleAddress parent block g count spectator
    readRoles address after = (Piece.remainder i.val).run (readRoles address before) := by
  dsimp only [ordinaryRoleAddress]
  apply idleCopies_modular_read (w+1) i _ before after _ off
  intro k e P x
  rw [idleExchange_axes _ (port_checked _ (idleRole i k).port.isLt) e.1 e.2]
  exact (reads k).exchange units block g live count (x ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) spectator

/-- Run the installed passes on their common bank and read the compiled idle
from the very same final store and summed step bound. -/
theorem ordinaryIdle_exec {w R W parents T Q : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2) → Stacks T prime → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        OriginalPortReads R W parents (idleInterval i k.2) parent
          (port (idleRole i k).port.val) (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x S u) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) ∧
      ∀ block g, IsUnit g → ∀ spectator, let address := ordinaryRoleAddress parent block g count spectator
        readRoles address y = (Piece.remainder i.val).run (readRoles address x) := by
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := idleCopies_exec i body program budget prepared ready
    (fun k => OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val))
    pass x S u input frames
  exact ⟨y,D,z,n,exec,paid,user,final,kept,fun block g live spectator =>
    ordinaryIdle_read i parent units block g live count spectator x y acts kept⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
