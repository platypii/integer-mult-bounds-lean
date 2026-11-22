module

public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleWindow

/-! Interpret the interleaved recursive output at the exact cells of a selected idle window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Stack Host
open Shared50ModularControl (prime)

private theorem castTransposeRead {v u : Descriptor} (same : v = u) {V : ℕ}
    (sv : volume prime v = V) (su : volume prime u = V) (x : Fin (volume prime v) → ZMod 2) (a : Fin (volume prime u)) :
    Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x
      ((a.cast su).cast sv.symm) =
    Shared50RecursiveNodeRows.transpose (one_dvd u.rows) (fun b => x ((b.cast su).cast sv.symm)) a := by
  subst u
  rfl

theorem idleInterleaved_read (i : Fin 9) (j : Fin 222) (w W : ℕ) :
    let e := idleInterval i j
    let lane := phaseIntervalChild (e.1+1) (e.2+1) w W 64
    let wide := {lane with afterD := lane.afterD*142080}
    let size := intervalChild_volume (Nat.succ_le_succ (idleBounds i j).1) (Nat.succ_le_succ (idleBounds i j).2) w (W*142080)
    let shape : wide = phaseIntervalChild (e.1+1) (e.2+1) w (W*142080) 64 := by
      simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
    let physical := (congrArg (volume prime) shape).trans size
    ∀ x : Fin (volume prime wide) → ZMod 2,
      parentIntervalRead i j w (W*142080) (fun k => x (k.cast physical.symm)) (fun k =>
        Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x
          (k.cast physical.symm)) := by
  intro e lane wide size shape physical x a
  exact castTransposeRead shape physical size x a

private theorem mergedPayload {T c m V : ℕ} (bank : Fin (((1+c)+2)+2) ↪ Fin T)
    (S : Stacks T prime) (word : Fin V → ZMod 2) (data : Fin c → Fin m → ZMod 2)
    (ready : RepT (intervalOwnerBank (putWord (fun _ => blank) 0
      (List.ofFn fun k => SparseRoleCircuit.encode (word k))) data) (embStk bank S).L (embStk bank S).R) :
    Cover.Fallback.RecordPayload (bank 0) (fun _ => blank) 0 word S := by
  intro z
  rw [encodedOwnerCell]
  have zero : ((((0 : Fin 1).castAdd c).castAdd 2).castAdd 2) = 0 := Fin.ext rfl
  rw [← zero]
  simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
    CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply] using
    (ready ((((0 : Fin 1).castAdd c).castAdd 2).castAdd 2) z).symm

private theorem castPayload {T m n : ℕ} (size : m = n) (port : Fin T) (S : Stacks T prime)
    (word : Fin n → ZMod 2) :
    Cover.Fallback.RecordPayload port (fun _ => blank) 0 (fun i => word (i.cast size)) S →
      Cover.Fallback.RecordPayload port (fun _ => blank) 0 word S := by
  subst n
  exact id

def IntervalRun {P U : Type} {N Q : ℕ} (seed : Stacks N prime) (price : ℕ) (lane : Descriptor)
    (reads : let wide := {lane with afterD := lane.afterD*142080}
             (Fin (volume prime wide) → ZMod 2) → (Fin (volume prime wide) → ZMod 2) → Prop) : Prop :=
    let T := intervalSplitTapes
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (program : Pr (Empty ⊕ P) H Q prime U),
    ∀ (x : Fin (volume prime wide) → ZMod 2) u S,
      S.R (caller 0) = List.ofFn (fun k : Fin (V*142080) => SparseRoleCircuit.encode (x (k.cast size))) →
      (∀ k, S.L (caller k) = []) → (∀ k, k ≠ 0 → S.R (caller k) = []) →
      (∀ k : Fin 142082, let t := (k.castAdd T).castAdd N
        S.L t = [] ∧ S.R t = []) →
      (∀ k : Fin N, let t := k.natAdd (142082+T)
        S.L t = seed.L k ∧ S.R t = seed.R k) →
      ∃ z F n, ∃ y : Fin (volume prime wide) → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(T+5)+5)*(V*142080)+24+((142081*(8*V+10)+1+price)+(149*(V*142080)*(T+5)+6)) ∧
        z.user = u.user ∧ reads x y ∧
        Cover.Fallback.RecordPayload (caller 0) (fun _ => blank) 0 y F

private theorem intervalRun_of_transpose {P U : Type} {N Q price : ℕ} (lane : Descriptor)
    (positiveV : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price) :
    let wide := {lane with afterD := lane.afterD*142080}
    ∀ reads, (∀ x, reads x (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x)) →
      IntervalRun (P := P) (U := U) (Q := Q) seed price lane reads := by
  intro wide reads effect
  obtain ⟨host,program,bank,target,run⟩ := inheritedInterval_exec lane positiveV capacity child
  refine ⟨host,program,?_⟩
  intro x u S source left empty fresh prepared
  obtain ⟨z,F,n,exec,paid,user,rows⟩ := run x u S source left empty fresh prepared
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,paid,user,effect x,?_⟩
  rw [← target]
  exact castPayload _ _ _ _ (mergedPayload bank F _ _ rows)

private theorem intervalVolume_pos {lo hi W : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (w : ℕ) (positive : 0 < W) : 0 < volume prime (phaseIntervalChild lo hi w W 64) := by
  rw [intervalChild_volume ordered fits]
  exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive

/-- The physical split, recursive child and merge discharge the chart's
single-copy read condition when the trailing spectator contains whole rows. -/
theorem inheritedIdleCopy_exec {P U : Type} {N Q price : ℕ}
    (i : Fin 9) (j : Fin 222) (w W : ℕ) (positive : 0 < W)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed} :
    let e := idleInterval i j
    let lane := phaseIntervalChild (e.1+1) (e.2+1) w W 64
    PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price →
    let wide := {lane with afterD := lane.afterD*142080}
    let shape : wide = phaseIntervalChild (e.1+1) (e.2+1) w (W*142080) 64 := by
      simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
    let physical := (congrArg (volume prime) shape).trans
      (intervalChild_volume (Nat.succ_le_succ (idleBounds i j).1) (Nat.succ_le_succ (idleBounds i j).2) w (W*142080))
    IntervalRun (P := P) (U := U) (Q := Q) seed price lane (fun x y =>
      parentIntervalRead i j w (W*142080) (fun k => x (k.cast physical.symm)) (fun k => y (k.cast physical.symm))) := by
  intro e lane child wide shape physical
  have positiveV := intervalVolume_pos (Nat.succ_le_succ (idleBounds i j).1)
    (Nat.succ_le_succ (idleBounds i j).2) w positive
  apply intervalRun_of_transpose lane positiveV capacity child
  intro x
  exact idleInterleaved_read i j w W x

/-- Run a private copy program with its target shared with one scheduled owner.
The other owners and the two volume counters retain their representations. -/
theorem placeIdleOwner_exec {P R U : Type} {T H Q c V : ℕ}
    (place : Fin T ↪ Fin H) (slot : Fin T) (fan : Fin (c+2) ↪ Fin H) (owner : Fin c)
    (shared : place slot = fan (owner.castAdd 2))
    (apart : ∀ i, i ≠ owner.castAdd 2 → ∀ j, place j ≠ fan i)
    (inner : P → Pr P T Q prime U) (host : R → Pr R H Q prime U) (label : P → R)
    (calls : ∀ p, host (label p) = embProg place label (inner p))
    (code : Pr P T Q prime U) (u : HS H Q prime U) (S : Stacks H prime)
    (x : Fin c → Fin V → ZMod 2) (live : HelperFan fan x S)
    (v : HS T Q prime U) (D : Stacks T prime) (n : ℕ) (y : Fin V → ZMod 2)
    (run : Exec inner code (mk (embDn place u) (embStk place S)) n (mk v D))
    (payload : Cover.Fallback.RecordPayload slot (fun _ => blank) 0 y D) :
    ∃ z F, Exec host (embProg place label code) (mk u S) n (mk z F) ∧ z.user = v.user ∧
      HelperFan fan (Function.update x owner y) F ∧
      ∀ t, (∀ j, place j ≠ t) → F.L t = S.L t ∧ F.R t = S.R t := by
  obtain ⟨z,F,exec,_,user,view,frame⟩ := exec_emb place.injective calls run u rfl S rfl
  refine ⟨z,F,exec,user,fanUpdate owner y live ?_ (fun i ne => frame _ (apart i ne)),frame⟩
  rw [← shared]
  change Cover.Fallback.RecordPayload slot (fun _ => blank) 0 y (embStk place F)
  rwa [view]

/-- Schedule disjoint copy workspaces. Each local execution starts with
exactly its original register stacks, even when earlier copies leave their
private workspaces occupied. -/
theorem placedIdleWindow_exec {H Q V : ℕ} {R U : Type} (i : Fin 9)
    (host : R → Pr R H Q prime U) (fan : Fin (142081+2) ↪ Fin H)
    (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks H prime) (u : HS H Q prime U)
    (live : HelperFan fan x S) :
    let Job := (Fin 32 × Fin 5) × Fin 222
    ∀ (T : Job → ℕ) (P : Job → Type) (place : ∀ k, Fin (T k) ↪ Fin H)
      (slot : ∀ k, Fin (T k)) (inner : ∀ k, P k → Pr (P k) (T k) Q prime U)
      (label : ∀ k, P k → R) (code : ∀ k, Pr (P k) (T k) Q prime U)
      (price : Job → ℕ) (effect : Job → (Fin V → ZMod 2) → (Fin V → ZMod 2) → Prop),
    (∀ k, place k (slot k) = fan ((idleTape i k).castAdd 2)) →
    (∀ k a, a ≠ (idleTape i k).castAdd 2 → ∀ j, place k j ≠ fan a) →
    (∀ k l, k ≠ l → ∀ j h, place k j ≠ place l h) →
    (∀ k p, host (label k p) = embProg (place k) (label k) (inner k p)) →
    (∀ k v (D : Stacks (T k) prime), (∀ j, D.L j = S.L (place k j) ∧ D.R j = S.R (place k j)) →
      ∃ z F n y, Exec (inner k) (code k) (mk v D) n (mk z F) ∧ n ≤ price k ∧
        z.user = v.user ∧ Cover.Fallback.RecordPayload (slot k) (fun _ => blank) 0 y F ∧
        effect k (x (idleTape i k)) y) →
    ∃ y F z n, Exec host (Prog.seqList (idleCopies.map fun k => embProg (place k) (label k) (code k)))
      (mk u S) n (mk z F) ∧ n ≤ (idleCopies.map price).sum+1 ∧ z.user = u.user ∧ HelperFan fan y F ∧
      (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  intro Job T P place slot inner label code price effect shared outside apart calls run
  let prepared := fun (k : Job) (_ : List Job) (D : Stacks H prime) =>
    ∀ j, D.L (place k j) = S.L (place k j) ∧ D.R (place k j) = S.R (place k j)
  let ready := fun (past : List Job) (y : Fin 142081 → Fin V → ZMod 2) (D : Stacks H prime) =>
    HelperFan fan y D ∧ ∀ k, k ∉ past → y (idleTape i k) = x (idleTape i k)
  obtain ⟨y,F,z,n,exec,paid,user,final,acts,off⟩ := idleCopies_exec i host _
    (fun k => (price k : ℝ)) prepared ready effect (by
      intro k past rest data D v order state fresh
      have unique : (past++k::rest).Nodup := order ▸ stageRuns_nodup.product (List.nodup_finRange _)
      have newJob : k ∉ past := fun h => (List.nodup_append.mp unique).2.2 k h k List.mem_cons_self rfl
      obtain ⟨b,G,m,word,ran,cost,same,payload,act⟩ := run k (embDn (place k) v) (embStk (place k) D) fresh
      obtain ⟨a,E,placed,user,owners,keep⟩ := placeIdleOwner_exec (place k) (slot k) fan (idleTape i k)
        (shared k) (outside k) (inner k) host (label k) (calls k) (code k) v D data state.1 b G m word ran payload
      refine ⟨Function.update data (idleTape i k) word,E,a,m,placed,by exact_mod_cast cost,
        user.trans same,⟨owners,?_⟩,?_,?_,fun t ne => Function.update_of_ne ne ..⟩
      · intro l hl
        simp only [List.mem_append,List.mem_singleton,not_or] at hl
        rw [Function.update_of_ne ((idleTape_injective i).ne hl.2)]
        exact state.2 l hl.1
      · intro l ne old j
        have frame := keep _ (fun h => apart k l ne.symm h j)
        exact ⟨frame.1.trans (old j).1,frame.2.trans (old j).2⟩
      · simpa only [Function.update_self,state.2 k newJob] using act)
    x S u ⟨live,fun _ _ => rfl⟩ (fun _ _ => ⟨rfl,rfl⟩)
  refine ⟨y,F,z,n,exec,?_,user,final.1,acts,off⟩
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_list_sum,List.map_map,Function.comp_def] using paid

end IntegerMultBounds.MathlibTM2.M6.BitNode
