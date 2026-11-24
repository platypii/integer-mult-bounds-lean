module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerSeedSequence
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Initialize every private basis bank in a compact phase, including the common
cutoff word in record slot 34. Shared owner tapes retain their contents. -/
theorem loadCompactWorkerSeeds [M8.Machine.Net] {P U : Type} {n H Q k : ℕ} (host : P → Pr P H Q prime U)
    (ts : Fin n → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i))
    (layout : ∀ i, WorkerBasisLayout (ports i)) (bank : ∀ i, Fin (ts i) ↪ Fin H)
    (owner : ∀ i, Fin k ↪ Fin (ts i)) (caller : Fin 6 ↪ Fin H) (cut : Fin H)
    (away : ∀ i j s, bank i j ≠ caller s) (offCut : ∀ i j, bank i j ≠ cut)
    (tmp : cut ≠ caller 4) (saved : cut ≠ caller 5)
    (owned : ∀ i, (layout i).OwnerTapes (owner i)) :
    let privateSlot := fun i (j : Fin (ts i)) => ∀ h, owner i h ≠ j
    (∀ i j, privateSlot i j → ∀ m, m ≠ i → ∀ l, bank m l ≠ bank i j) →
    ∃ code, ∀ w W u (S : Stacks H prime),
      let M := prime^(w+1)
      0 < W → S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i j, privateSlot i j → S.L (bank i j) = [] ∧ S.R (bank i j) = []) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (178*n*(M^16*W)+n*(8*(S.R cut).length+6)+2) ∧
        (∀ i j, privateSlot i j → let seed := (layout i).seed w W (S.R cut)
          F.L (bank i j) = seed.L j ∧ F.R (bank i j) = seed.R j) ∧
        ∀ j, (∀ i l, privateSlot i l → bank i l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro priv separate
  let slot i := scheduledRecordPorts (ports i) 34
  have privateCut i : priv i (slot i) := (owned i).recordPrivate _ (by change (34 : ℕ) ≠ 24; decide)
  let dst : Fin n ↪ Fin H := ⟨fun i => bank i (slot i),fun i j eq => by
    by_contra ne
    exact separate i _ (privateCut i) j (Ne.symm ne) _ eq.symm⟩
  obtain ⟨setup,prepare⟩ := loadStageWorkerSeeds host ts ports layout bank owner caller away
    (List.finRange n) (List.nodup_finRange n) owned separate
  obtain ⟨fill,write⟩ := installChildSeed host dst (Function.Embedding.refl _) (fun _ => cut)
    (caller 4) (caller 5) (fun i _ => offCut i _) (fun i => by
      change [cut,bank i (slot i),caller 4,caller 5].Nodup
      simp [List.nodup_cons,(offCut i _).symm,away,tmp,saved,caller.injective.eq_iff])
  refine ⟨setup.seq fill,?_⟩
  intro w W u S M pos modulus tail unit atom ht hs blank
  obtain ⟨v,D,a,start,user,paid,stock,frame⟩ := prepare w W u S pos modulus tail unit atom ht hs
    (fun i _ j => blank i j)
  let seed : Stacks n prime := ⟨[],[],fun _ => [],fun _ => S.R cut⟩
  have initialized i j (off : priv i j) := stock i (List.mem_finRange i) j off (S.R cut)
  have src := frame cut (fun i _ j _ => offCut i j)
  have keep s := frame (caller s) (fun i _ j _ => away i j s)
  obtain ⟨z,R,b,finish,same,cost,loaded,rest⟩ := write seed v D (fun _ => src.2)
    (fun i => by change D.R (bank i (slot i)) = []; simpa [slot] using (initialized i _ (privateCut i)).2)
    ((keep 4).2.trans ht) ((keep 5).2.trans hs)
  refine ⟨z,_,a+b,start.seq finish,same.trans user,?_,?_,?_⟩
  · have h := paid.seq cost
    convert h using 1
    simp [seedLoadBill,seed,M]
    omega
  · intro i j off
    have init := initialized i j off
    refine ⟨init.1,?_⟩
    by_cases hit : j = slot i
    · subst j
      have h := loaded i (fun ne => False.elim (ne i rfl))
      simpa [seed,dst,slot,WorkerBasisLayout.seed,recordBasisStacks,embExt_apply (ports i).injective,
        scheduledRecordPorts,moveRecordSeed] using h
    · have untouched m : dst m ≠ bank i j := by
        by_cases eq : m = i
        · subst m; exact (bank i).injective.ne (Ne.symm hit)
        · exact separate i j off m eq _
      exact (rest _ untouched).trans (by simpa [slot,Function.update_of_ne hit] using init.2)
  · intro j outside
    have keep := frame j (fun i _ => outside i)
    exact ⟨keep.1,(rest j (fun i => outside i _ (privateCut i))).trans keep.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
