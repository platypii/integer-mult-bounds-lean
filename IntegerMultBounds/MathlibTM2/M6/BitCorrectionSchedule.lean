module

public import IntegerMultBounds.MathlibTM2.M6.BitChartInitialization
public import IntegerMultBounds.MathlibTM2.M6.BitSweepPortCorrection

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback
open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- All active port corrections share the swap workspace. Only the payload
register varies across calls, and each correction pays its own leaf bill. -/
theorem workerPortCorrectionList [M8.Machine.Net] {ι : Type} (port : ι → Fin 111) (atExit : Bool) :
    ∃ q k : Fin 111 → ℕ, ∀ {P U : Type} {T K Q : ℕ}
      (body : P → Pr P (T+(24+K)) Q prime U) (record : ι → Fin 35 ↪ Fin T) (width : Fin T),
      (∀ t, q t ≤ Q) → (∀ t, k t ≤ K) → (∀ r i, width ≠ record r i) →
      (∀ r s, r ≠ s → ∀ i, record r i ≠ record s 24) →
      ∀ jobs : List ι, jobs.Nodup →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let io := fun r => (record r 24).castAdd (24+K)
      ∀ (x : ι → Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      (∀ r (i : Fin 35), i ≠ 24 → S.R ((record r i).castAdd _) = (moveRecordSeed w W [] [] []).R (small i)) →
      S.R (width.castAdd _) = binSyms (w+1).size (w+1) →
      (∀ r h, readAt blank (S.L (io r)) (S.R (io r)) h = (portOwner (x r)).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ y : ι → Fin V → ZMod 2, ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ∧
        (∀ r h, readAt blank (F.L (io r)) (F.R (io r)) h = (portOwner (y r)).tape 0 h) ∧
        (∀ r ∈ jobs, ∀ s j, let t := port r
                let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
                let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
                let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
                let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
                  else M8.Exchange.exchange A (M8.Exchange.exchange B s)
                y r (FlatCoordinateLayout.index (embed s) j) = x r (FlatCoordinateLayout.index (embed moved) j)) ∧
        (∀ r ∉ jobs, y r = x r) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, (∀ r ∈ jobs, j ≠ record r 24) →
          F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  classical
  choose q k worker using fun t => runWorkerPortCorrection t atExit
  refine ⟨q,k,?_⟩
  intro P U T K Q body record width states room outside apart jobs unique
  choose code rate coreRate run using fun r => worker (port r) (states _) (room _) body (record r) width (outside r)
  induction jobs with
  | nil =>
    refine ⟨.act .done,1,0,?_⟩
    intro w W pos M V small io x u S stock prec live free
    refine ⟨x,u,S,1,Exec.act ..,rfl,?_,live,by simp,by simp,free,fun _ _ => ⟨rfl,rfl⟩⟩
    have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
    intro js nd
    simp only [one_mul,zero_mul,add_zero]
    omega
  | cons r jobs ih =>
    obtain ⟨rest,a,b,tail⟩ := ih unique.tail
    refine ⟨(code r).seq rest,rate r+a,coreRate r+b,?_⟩
    intro w W pos M V small io x u S stock prec live free
    obtain ⟨row,v,D,n,start,user,paid,out,action,empty,off⟩ :=
      run r w W pos [] [] [] (x r) u S (stock r) prec (live r) free
    let next := Function.update x r row
    have away (s i) (hi : i ≠ 24) : record s i ≠ record r 24 := by
      by_cases eq : s = r
      · subst s; exact (record r).injective.ne hi
      · exact apart s r eq i
    obtain ⟨y,z,F,m,finish,last,bill,done,move,keep,blank,frame⟩ :=
      tail w W pos next v D (fun s i hi => (off _ (away s i hi)).2.trans (stock s i hi))
        ((off width (outside r 24)).2.trans prec) (by
          intro s
          by_cases eq : s = r
          · subst s; simpa [next] using out
          · have h := off _ (apart s r eq 24)
            change ∀ j, readAt _ (D.L ((record s 24).castAdd _)) (D.R ((record s 24).castAdd _)) j = _
            rw [h.1,h.2,show next s = x s from Function.update_of_ne eq ..]
            exact live s) empty
    refine ⟨y,z,F,n+m,start.seq finish,last.trans user,?_,done,?_,?_,blank,?_⟩
    · simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using paid.seq bill
    · intro s hs
      rcases List.mem_cons.mp hs with eq|mem
      · subst s
        rw [keep r unique.notMem,show next r = row from Function.update_self ..]
        exact action
      · have ne : s ≠ r := fun eq => unique.notMem (eq ▸ mem)
        simpa only [next,Function.update_of_ne ne] using move s mem
    · intro s hs
      exact (keep s (fun h => hs (List.mem_cons_of_mem _ h))).trans
        (Function.update_of_ne (show s ≠ r from fun eq => hs (eq ▸ List.mem_cons_self)) ..)
    · intro j hj
      have h := off j (hj r List.mem_cons_self)
      have g := frame j (fun s mem => hj s (List.mem_cons_of_mem _ mem))
      exact ⟨g.1.trans h.1,g.2.trans h.2⟩

/-- Run all 160 × 111 inverse port corrections on the selected owners using
one record and one reusable scratch bank, with uniform finite capacities. -/
theorem scheduledWorkerCorrections [M8.Machine.Net] (atExit : Bool) :
    ∃ states space : ℕ, ∀ {P U : Type} {T K Q : ℕ}
      (body : P → Pr P (T+(24+K)) Q prime U) (record : Fin 35 ↪ Fin T)
      (owners : ((Fin 32 × Fin 5) × Fin 111) ↪ Fin T) (width : Fin T),
      states ≤ Q → space ≤ K → (∀ i, width ≠ record i) → (∀ r, width ≠ owners r) →
      (∀ i r, record i ≠ owners r) →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let io := fun r => (owners r).castAdd (24+K)
      ∀ (x : ((Fin 32 × Fin 5) × Fin 111) → Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      (∀ (i : Fin 35), i ≠ 24 → S.R ((record i).castAdd _) = (moveRecordSeed w W [] [] []).R (small i)) →
      S.R (width.castAdd _) = binSyms (w+1).size (w+1) →
      (∀ r h, readAt blank (S.L (io r)) (S.R (io r)) h = (portOwner (x r)).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ y : ((Fin 32 × Fin 5) × Fin 111) → Fin V → ZMod 2, ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ∧
        (∀ r h, readAt blank (F.L (io r)) (F.R (io r)) h = (portOwner (y r)).tape 0 h) ∧
        (∀ r, ∀ s j, let t := r.2
                let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
                let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
                let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
                let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
                  else M8.Exchange.exchange A (M8.Exchange.exchange B s)
                y r (FlatCoordinateLayout.index (embed s) j) = x r (FlatCoordinateLayout.index (embed moved) j)) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        ∀ j : Fin T, (∀ r, j ≠ owners r) →
          F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  classical
  obtain ⟨q,k,build⟩ := workerPortCorrectionList (fun r : (Fin 32 × Fin 5) × Fin 111 => r.2) atExit
  obtain ⟨states,qs⟩ := Finite.exists_le q
  obtain ⟨space,ks⟩ := Finite.exists_le k
  refine ⟨states,space,?_⟩
  intro P U T K Q body record owners width cap room ext clock apart
  let regs r := chartLivePorts record 24 (owners r) (fun i => apart i r)
  have owner r : regs r 24 = owners r := by simp [regs,chartLivePorts]
  have other r i (ne : i ≠ 24) : regs r i = record i := by simp [regs,chartLivePorts,ne]
  let jobs := stageRuns.product (List.finRange 111)
  have mem (r : (Fin 32 × Fin 5) × Fin 111) : r ∈ jobs :=
    List.mem_flatMap.mpr ⟨r.1,mem_stageRuns _,List.mem_map.mpr ⟨r.2,List.mem_finRange _,rfl⟩⟩
  obtain ⟨code,a,b,run⟩ := build body regs width (fun t => (qs t).trans cap)
    (fun t => (ks t).trans room) (by
      intro r i
      by_cases eq : i = 24
      · subst i; rw [owner]; exact clock r
      · rw [other r i eq]; exact ext i) (by
      intro r s ne i
      rw [owner s]
      by_cases eq : i = 24
      · subst i; rw [owner]; exact owners.injective.ne ne
      · rw [other r i eq]; exact apart i s) jobs (stageRuns_nodup.product (List.nodup_finRange _))
  refine ⟨code,a,b,?_⟩
  intro w W pos M V small io x u S stock prec live free
  obtain ⟨y,z,F,n,exec,user,paid,out,action,_,empty,frame⟩ := run w W pos x u S
    (fun r i hi => by rw [other r i hi]; exact stock i hi) prec (by simpa only [owner] using live) free
  exact ⟨y,z,F,n,exec,user,paid,by simpa only [owner] using out,fun r => action r (mem r),empty,
    fun j hj => frame j (fun r _ => (owner r).symm ▸ hj r)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
