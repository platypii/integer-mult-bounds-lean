module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerPrivateSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Initialize the private tapes of a list of stage occurrences on their
assigned host banks. The occurrences share the caller's four dimension words
and two scratch tapes. Owner tapes may coincide across occurrences. -/
theorem loadStageWorkerSeeds [M8.Machine.Net] {I P U : Type} {H Q k : ℕ} (body : P → Pr P H Q prime U)
    (ts : I → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i))
    (layout : ∀ i, WorkerBasisLayout (ports i)) (bank : ∀ i, Fin (ts i) ↪ Fin H)
    (owner : ∀ i, Fin k ↪ Fin (ts i)) (caller : Fin 6 ↪ Fin H)
    (away : ∀ i j s, bank i j ≠ caller s) (order : List I) (distinct : order.Nodup) :
    let privateSlot := fun i (j : Fin (ts i)) => ∀ h, owner i h ≠ j
    (∀ i, (layout i).OwnerTapes (owner i)) →
    (∀ i j, privateSlot i j → ∀ m, m ≠ i → ∀ l, bank m l ≠ bank i j) →
    ∃ code, ∀ w W u (S : Stacks H prime),
      let M := prime^(w+1)
      0 < W → S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i ∈ order, ∀ j, privateSlot i j → S.L (bank i j) = [] ∧ S.R (bank i j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (178*order.length*(M^16*W)+1) ∧
        (∀ i ∈ order, ∀ j, privateSlot i j → ∀ record, let seed := (layout i).seed w W record
          F.L (bank i j) = seed.L j ∧ F.R (bank i j) = Function.update seed.R (scheduledRecordPorts (ports i) 34) [] j) ∧
        ∀ j, (∀ i ∈ order, ∀ l, privateSlot i l → bank i l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro priv owned separate
  induction order with
  | nil =>
    refine ⟨.act .done,?_⟩
    intro w W u S M _ _ _ _ _ _ _ _
    exact ⟨u,S,1,Exec.act .done _,rfl,by intro js nd; simp [Nat.add_comm],by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons i rest ih =>
    obtain ⟨first,load⟩ := loadWorkerPrivateSeed body (bank i) caller (away i) (ports i) (layout i)
    obtain ⟨tail,run⟩ := ih distinct.tail
    refine ⟨first.seq tail,?_⟩
    intro w W u S M pos modulus spectator unit atom ht hs empty
    have blank := empty i List.mem_cons_self
    obtain ⟨v,D,n,start,user,paid,_,_,stock,frame⟩ := load w W u S pos modulus spectator unit atom ht hs
      (fun j ne => blank _ ((owned i).recordPrivate j ne)) (fun side j => by
        cases side with
        | false => exact blank _ ((owned i).reversePrivate j)
        | true => exact blank _ ((owned i).forwardPrivate j))
    have kept j (off : ∀ l, priv i l → bank i l ≠ j) :=
      frame j (fun l ne => off _ ((owned i).recordPrivate l ne)) (fun side l => by
        cases side with
        | false => exact off _ ((owned i).reversePrivate l)
        | true => exact off _ ((owned i).forwardPrivate l))
    have source s := kept (caller s) (fun l _ => away i l s)
    have other m (hm : m ∈ rest) : m ≠ i := fun eq => distinct.notMem (eq ▸ hm)
    obtain ⟨z,F,t,finish,same,cost,stored,last⟩ := run w W v D pos ((source 0).2.trans modulus)
      ((source 1).2.trans spectator) ((source 2).2.trans unit) ((source 3).2.trans atom)
      ((source 4).2.trans ht) ((source 5).2.trans hs) (fun m hm j privateTape => by
        have preserve := kept (bank m j) (fun l hl => (separate i l hl m (other m hm) j).symm)
        have clear := empty m (List.mem_cons_of_mem _ hm) j privateTape
        exact ⟨preserve.1.trans clear.1,preserve.2.trans clear.2⟩)
    refine ⟨z,F,n+t,start.seq finish,same.trans user,?_,?_,?_⟩
    · convert paid.seq cost using 1
      simp only [List.length_cons]
      ring
    · intro m hm j privateTape archive
      rcases List.mem_cons.mp hm with rfl | hm
      · have fresh := blank j privateTape
        have initialized := stock j (fun l eq h => by
          obtain ⟨o,ho⟩ := (owned _).payload l eq
          exact privateTape o (ho.trans h)) (fun _ _ => fresh) archive
        have preserve := last _ (fun l hl a _ => separate _ j privateTape l (other l hl) a)
        exact ⟨preserve.1.trans initialized.1,preserve.2.trans initialized.2⟩
      · exact stored m hm j privateTape archive
    · intro j off
      have a := kept j (off _ List.mem_cons_self)
      have b := last j (fun m hm => off m (List.mem_cons_of_mem _ hm))
      exact ⟨b.1.trans a.1,b.2.trans a.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
