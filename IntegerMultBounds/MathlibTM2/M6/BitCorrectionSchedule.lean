module

public import IntegerMultBounds.MathlibTM2.M6.BitChartInitialization
public import IntegerMultBounds.MathlibTM2.M6.BitSweepPortCorrection

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback
open Matrix AffineFieldCoordinates IntegerMultBounds.Swap.Modular
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Read equation for the inverse correction on one active port. -/
def PortCorrectionRead (t : Fin 111) (atExit : Bool) (w W : ℕ)
    (x y : Fin ((prime^(w+1))^16*W) → ZMod 2) : Prop :=
  let M := prime^(w+1)
  let A := translatedPortProjector (ZMod M) (4:ZMod M)⁻¹ t
  let B := reduce M (selectedProjector ⟨2+t.val,by omega⟩)
  let E := reduce M (selectedProjector ⟨525+t.val,by omega⟩)
  ∀ s j, let moved := if atExit then M8.Exchange.exchange E (M8.Exchange.exchange (1-A) s)
    else M8.Exchange.exchange A (M8.Exchange.exchange B s)
    y (FlatCoordinateLayout.index (embed s) j) = x (FlatCoordinateLayout.index (embed moved) j)

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
        (∀ r ∈ jobs, PortCorrectionRead (port r) atExit w W (x r) (y r)) ∧
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
        (∀ r, PortCorrectionRead r.2 atExit w W (x r) (y r)) ∧
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

/-- The entry pass acts on source owners and the exit pass on target owners. -/
noncomputable def activeCorrectionOwners (n : Fin 9) (atExit : Bool) :
    ((Fin 32 × Fin 5) × Fin 111) ↪ Fin 142081 :=
  if atExit then ⟨targetOwner n,targetOwner_injective n⟩ else ⟨sourceOwner n,source_injective n⟩

/-- Initialize the single shared record from caller words and run the entire
selected pass. Only the selected owners and the record bank can change. -/
theorem initializeScheduledCorrections [M8.Machine.Net] (n : Fin 9) (atExit : Bool) :
    ∃ states space : ℕ, ∀ {P U : Type} {T K Q : ℕ}
      (body : P → Pr P (T+(24+K)) Q prime U) (place : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fan : Fin 142081 ↪ Fin T) (caller : Fin 6 ↪ Fin T),
      let owners := (activeCorrectionOwners n atExit).trans fan
      states ≤ Q → space ≤ K → (∀ i j, place i ≠ caller j) → (∀ i j, place i ≠ fan j) →
      (∀ r, caller 3 ≠ owners r) →
      ∃ code rate coreRate, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^16*W
      let io := fun r => (owners r).castAdd (24+K)
      ∀ (x : ((Fin 32 × Fin 5) × Fin 111) → Fin V → ZMod 2) u (S : Stacks (T+(24+K)) prime),
      S.R ((caller 0).castAdd _) = binSyms M.size M → S.R ((caller 1).castAdd _) = binSyms W.size W →
      S.R ((caller 2).castAdd _) = binSyms 1 1 → S.R ((caller 3).castAdd _) = binSyms (w+1).size (w+1) →
      S.R ((caller 4).castAdd _) = [] → S.R ((caller 5).castAdd _) = [] →
      (∀ i, i.val ≠ 24 → S.L ((place i).castAdd _) = [] ∧ S.R ((place i).castAdd _) = []) →
      (∀ r h, readAt blank (S.L (io r)) (S.R (io r)) h = (portOwner (x r)).tape 0 h) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ y : ((Fin 32 × Fin 5) × Fin 111) → Fin V → ZMod 2, ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ∧
        (∀ r h, readAt blank (F.L (io r)) (F.R (io r)) h = (portOwner (y r)).tape 0 h) ∧
        (∀ r, PortCorrectionRead r.2 atExit w W (x r) (y r)) ∧
        (∀ j : Fin (24+K), F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = []) ∧
        (∀ i, i.val ≠ 24 → let seed := moveRecordSeed w W [] [] []
          F.L ((place i).castAdd _) = seed.L i ∧ F.R ((place i).castAdd _) = seed.R i) ∧
        ∀ j : Fin T, (∀ r, j ≠ owners r) → (∀ i, place i ≠ j) →
          F.L (j.castAdd _) = S.L (j.castAdd _) ∧ F.R (j.castAdd _) = S.R (j.castAdd _) := by
  obtain ⟨states,space,build⟩ := scheduledWorkerCorrections atExit
  refine ⟨states,space,?_⟩
  intro P U T K Q body place fan caller owners cap room external disjoint clock
  let ext := Fin.castAddEmb (n := T) (24+K)
  let src := fun i : Fin 3 => ext (caller (i.castAdd 3))
  obtain ⟨init,load⟩ := loadWorkerRecordSeed body (place.trans ext) src (ext (caller 3))
    (ext (caller 4)) (ext (caller 5)) (fun i => ext.injective.ne (external _ _).symm)
    (fun i j => ext.injective.ne (external _ _)) (by
      intro i
      have a : i.castAdd 3 ≠ (4 : Fin 6) := by fin_cases i <;> decide
      have b : i.castAdd 3 ≠ (5 : Fin 6) := by fin_cases i <;> decide
      have distinct (j) : [caller (i.castAdd 3),place j,caller 4,caller 5].Nodup := by
        simp [List.nodup_cons,caller.injective.eq_iff,(external j _).symm,external j,a,b]
      exact (distinct _).map ext.injective)
  obtain ⟨code,rate,coreRate,run⟩ := build body (scheduledRecordPorts place) owners (caller 3) cap room
    (fun i => (external _ _).symm) clock (fun i r => disjoint _ _)
  refine ⟨init.seq code,rate+98,coreRate,?_⟩
  intro w W pos M V io x u S modulus count unit prec tmp saved vacant live free
  obtain ⟨v,D,t,start,user,paid,stock,off⟩ := load w W u S modulus count unit prec vacant tmp saved
  have keep r := off (io r) (fun i _ => ext.injective.ne (disjoint i _))
  have clean j := off (Fin.natAdd T j) (fun i _ eq => by
    have h := congrArg Fin.val eq
    change (place i).val = T+j.val at h
    have := (place i).isLt
    omega)
  obtain ⟨y,z,F,m,finish,last,bill,out,action,empty,frame⟩ := run w W pos x v D
    (fun i ne => (stock _ (fun eq => ne (Fin.ext eq))).2)
    ((off _ (fun i _ => ext.injective.ne (external i 3))).2.trans prec)
    (fun r h => by rw [(keep r).1,(keep r).2]; exact live r h)
    (fun j => ⟨(clean j).1.trans (free j).1,(clean j).2.trans (free j).2⟩)
  refine ⟨y,z,F,t+m,start.seq finish,last.trans user,?_,out,action,empty,?_,?_⟩
  · have mass : M ≤ V := (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ pos)
    have width : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
    have spectators : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    have size (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
    intro js nd
    apply ((paid.seq bill) js nd).trans
    apply Nat.add_le_add_left
    change 18*M.size+8*W.size+8*(w+1)+11*(w+1).size+53+(rate*V+coreRate*M8.RevMachine.LeafCore.coreCost V (w+1)) ≤ (rate+98)*V+_
    nlinarith only [(size M).trans mass,(size W).trans spectators,width,(size _).trans width,pos.trans_le spectators]
  · intro i ne
    have same := frame (place i) (fun r => disjoint i _)
    exact ⟨same.1.trans (stock i ne).1,same.2.trans (stock i ne).2⟩
  · intro j away outside
    have a := frame j away
    have b := off (ext j) (fun i _ => ext.injective.ne (outside i))
    exact ⟨a.1.trans b.1,a.2.trans b.2⟩

/-- The scheduled reads on the physical source and target owners implement
the active part of the borrowed sweep at every independent matrix label. -/
theorem correctedBorrowedPortReads (n : Fin 9) (w B K : ℕ)
    (x entry middle output : Fin 142081 → Fin ((prime^(w+1))^16*(B*prime^(64*((w+1)*64))*K)) → ZMod 2)
    (enter : ∀ (r : (Fin 32 × Fin 5) × Fin 111), PortCorrectionRead r.2 false w _ (x (sourceOwner n r)) (entry (sourceOwner n r)))
    (leave : ∀ (r : (Fin 32 × Fin 5) × Fin 111), PortCorrectionRead r.2 true w _ (middle (targetOwner n r)) (output (targetOwner n r)))
    (keepTarget : ∀ r, entry (targetOwner n r) = x (targetOwner n r))
    (keepSource : ∀ r, output (sourceOwner n r) = middle (sourceOwner n r))
    (ports : BorrowedPorts n (w+1) B K entry middle) :
    ∀ (r : (Fin 32 × Fin 5) × Fin 111) (g : LabelPadding.Label 64 (w+1)) (z : LabelEntry.Cell (copyLabelLayout (w+1) B K) B) s,
      let cell := fun v => FlatCoordinateLayout.index (embed v) (labelSpectator g z)
      let P := translatedPortProjector (ZMod (prime^(w+1))) (4 : ZMod (prime^(w+1)))⁻¹ r.2
      output (sourceOwner n r) (cell s) = x (sourceOwner n r) (cell (M8.Exchange.exchange P s.swap)) ∧
      output (targetOwner n r) (cell s) = x (targetOwner n r) (cell (M8.Exchange.exchange (1-P) s)) +
        x (sourceOwner n r) (cell s.swap) := by
  intro r g z s cell P
  obtain ⟨src,dst⟩ := ports r.1 r.2 g z
  rw [keepSource]
  exact correctedSweep_reads (w+1) _ r.2 n r.1 x entry middle (output (targetOwner n r)) (labelSpectator g z)
    (fun v => enter r v _) (keepTarget r) dst src (fun v => leave r v _) s

end IntegerMultBounds.MathlibTM2.M6.BitNode
