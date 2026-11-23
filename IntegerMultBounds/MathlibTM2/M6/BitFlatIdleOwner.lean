module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleReturn

/-! Schedule a private split–merge worker on an inherited owner and restore its caller frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)

/-- The merge growth estimate converts the lane worker's retained cells into
the cleanup budget consumed by the owner wrapper. -/
theorem mergedOwnerCleanup_le {T : ℕ} (bank : List (Fin T)) (E F : Stacks T prime) (V : ℕ)
    (growth : ∀ j ∈ bank, (F.L j).length+(F.R j).length ≤ (E.L j).length+(E.R j).length+298*V) :
    (bank.map fun j => 4*(F.L j).length+2*(F.R j).length+4).sum ≤
      4*(bank.map fun j => (E.L j).length+(E.R j).length).sum + bank.length*(1192*V+4) := by
  induction bank with
  | nil => simp
  | cons j rest ih =>
    have head := growth j List.mem_cons_self
    have tail := ih (fun t ht => growth t (List.mem_cons_of_mem _ ht))
    rw [Nat.mul_add] at tail
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.mul_add,one_mul]
    omega

theorem idleOwnerWorker_exec {P U : Type} {T Q V m B : ℕ} [NeZero B] (body : P → Pr P T Q prime U)
    (worker : Pr P T Q prime U) (bank : Fin B ↪ Fin T)
    (owner count saved tmp : Fin T) (apart : [count,bank 0,owner,saved,tmp].Nodup)
    (span : m*142080 = V) (word : Fin V → ZMod 2)
    (effect : (Fin V → ZMod 2) → Prop) (price : ℕ) :
    let slots := (List.finRange B).map bank
    owner ∉ slots → count ∉ slots → saved ∉ slots → tmp ∉ slots →
    let write := (loadCompactWord (bank 0) tmp count).seq
      (((usub count owner tmp).seq (movePrefix count (bank 0) owner saved tmp)).seq (bclear count))
    ∀ u S, RecordPayload owner (fun _ => blank) 0 word S →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) →
      S.R count = [] → S.R saved = [] → S.L tmp = [] → S.R tmp = [] →
      (∀ v D, D.R (bank 0) = List.ofFn (fun a : Fin (m*142080) => SparseRoleCircuit.encode (word (a.cast span))) →
        (∀ j, D.L (bank j) = []) → (∀ j, j ≠ 0 → D.R (bank j) = []) →
        ∃ z F n changed, Exec body worker (mk v D) n (mk z F) ∧ z.user = v.user ∧
          effect changed ∧ RecordPayload (bank 0) (fun _ => blank) 0 changed F ∧
          n+(slots.map fun j => 4*(F.L j).length+2*(F.R j).length+4).sum ≤ price ∧
          ∀ j, j ∉ slots → F.L j = D.L j ∧ F.R j = D.R j) →
      ∃ z F n changed, Exec body ((loadCompactWord owner tmp (bank 0)).seq (worker.seq (write.seq (clearWorkTapes slots))))
        (mk u S) n (mk z F) ∧ n ≤ price+28*V+33 ∧ z.user = u.user ∧
        effect changed ∧ RecordPayload owner (fun _ => blank) 0 changed F ∧
        ((F.L owner).length ≤ (S.L owner).length ∧ (F.R owner).length ≤ (S.R owner).length) ∧
        ∀ j, j ≠ owner → F.L j = S.L j ∧ F.R j = S.R j := by
  intro slots ho hc hs ht write u S input free count0 saved0 tmpL tmpR act
  have regs := apart
  regs_ne regs
  have member (j) : bank j ∈ slots := List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩
  obtain ⟨v,D,load,user,exactWord,left,right,unchanged⟩ := loadIdleSplit_exec body bank owner tmp
    (by simp [‹owner ≠ tmp›,‹bank 0 ≠ owner›.symm,‹bank 0 ≠ tmp›.symm]) span word u S input ⟨tmpL,tmpR⟩ free
  obtain ⟨y,G,k,changed,run,same,correct,merged,space,off⟩ := act v D exactWord left right
  have keep j (h : j ∉ slots) : G.L j = S.L j ∧ G.R j = S.R j := by
    have a := off j h
    have b := unchanged j (fun eq => h (eq ▸ member 0))
    exact ⟨a.1.trans b.1,a.2.trans b.2⟩
  have old : RecordPayload owner (fun _ => blank) 0 word G := by
    simpa only [RecordPayload,(keep owner ho).1,(keep owner ho).2] using input
  obtain ⟨z,F,l,finish,paid,hz,out,lengths,clean,rest⟩ := returnIdleBankWithStock_exec body apart slots
    ((List.nodup_finRange _).map bank.injective) (member 0) ho word changed y G old merged
    ((keep count hc).2.trans count0) ((keep saved hs).2.trans saved0)
    ((keep tmp ht).1.trans tmpL) ((keep tmp ht).2.trans tmpR)
  refine ⟨z,F,_,changed,Exec.seq load (Exec.seq run finish),by omega,hz.trans (same.trans user),correct,out,?_,?_⟩
  · simpa only [(keep owner ho).1,(keep owner ho).2] using lengths owner
  intro j ne
  by_cases inside : j ∈ slots
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp inside
    have h := clean _ (member a)
    exact ⟨h.1.trans (free a).1.symm,h.2.trans (free a).2.symm⟩
  · have h := rest j ne inside
    exact ⟨h.1.trans (keep j inside).1,h.2.trans (keep j inside).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
