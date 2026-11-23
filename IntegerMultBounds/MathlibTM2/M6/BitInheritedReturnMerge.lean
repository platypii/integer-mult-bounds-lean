module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

/-! Merge the inherited recursive child's returned rows on the caller's target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

def mergeSaved (c : ℕ) : Fin 3 ↪ Fin (((1+c)+2)+2) where
  toFun := Fin.cases 0 (fun j => (j.natAdd (1+c)).castAdd 2)
  inj' := by
    intro i j
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp only [Fin.cases_zero,Fin.cases_succ] <;>
      intro eq <;> first | trivial | apply Fin.ext <;> have h := congrArg Fin.val eq <;>
      simp only [Fin.val_zero,Fin.val_succ,Fin.val_castAdd,Fin.val_natAdd] at * <;> omega

private theorem mergeSaved_outside (c : ℕ) (k : Fin 3) (i : Fin 2) :
    intervalOwners c (i.natAdd c) ≠ mergeSaved c k := by
  induction k using Fin.cases with
  | zero =>
    intro eq
    have h := congrArg Fin.val eq
    change (intervalOwners c (i.natAdd c)).val = 0 at h
    simp [intervalOwners] at h
  | succ j =>
    intro eq
    have h := congrArg Fin.val eq
    change (intervalOwners c (i.natAdd c)).val = 1+c+j.val at h
    simp [intervalOwners] at h
    omega

theorem mergeSaved_outsideFan (c : ℕ) (k : Fin 3) (i : Fin (c+2)) :
    intervalOwners c i ≠ mergeSaved c k := by
  induction i using Fin.addCases with
  | right j => exact mergeSaved_outside c k j
  | left r =>
    induction k using Fin.cases with
    | zero =>
      intro eq
      have h := congrArg Fin.val eq
      change (intervalOwners c (r.castAdd 2)).val = 0 at h
      simp [intervalOwners] at h
      all_goals omega
    | succ j =>
      intro eq
      have h := congrArg Fin.val eq
      change (intervalOwners c (r.castAdd 2)).val = 1+c+j.val at h
      simp [intervalOwners] at h
      all_goals omega

/-- Sequence an owner-row computation with the physical merge. Only the
target and two inner counters must survive the computation on their saved tapes. -/
theorem mergeAfterReturnedRows {P U : Type} {T Q V price : ℕ}
    (host : P → Pr P T Q prime U) (program : Pr P T Q prime U)
    (saved : Fin 3 ↪ Fin T) (returned : Fin (142080+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ returned j)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < V) (target : ℤ → Fin (prime+4))
    (data output : Fin 142080 → Fin V → ZMod 2) (before : Stacks intervalSplitTapes prime)
    (u : HS T Q prime U) (S : Stacks T prime)
    (split : RepT (intervalOwnerBank target data) before.L before.R)
    (run : ∃ v D k, Exec host program (mk u S) k (mk v D) ∧ k ≤ price ∧ v.user = u.user ∧
      HelperFan returned output D ∧ ∀ i, D.L (saved i) = before.L (mergeSaved 142080 i) ∧
        D.R (saved i) = before.R (mergeSaved 142080 i)) :
    let bank := returnedMergeBank saved returned apart
    let merge := embProg bank Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
    let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                          SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
    ∃ z F n, Exec host (program.seq merge) (mk u S) n (mk z F) ∧
      n ≤ price+(149*(V*142080)*(intervalSplitTapes+5)+6) ∧ z.user = u.user ∧
      RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output) (embStk bank F).L (embStk bank F).R := by
  intro bank merge word
  obtain ⟨v,D,k,exec,paid,user,owners,frame⟩ := run
  obtain ⟨z,F,n,ran,bill,same,result,_,_⟩ := placedMergeReturnedOwners_exec host bank capacity positive
    target data output before v D split (by
      rw [show (intervalOwners 142080).trans bank = returned from returnedMergeBank_owners _ _ _]
      exact owners) (by
      rw [show bank 0 = saved 0 from returnedMergeBank_target _ _ _]
      exact frame 0) (fun j => by
      dsimp only
      rw [show bank ((j.natAdd (1+142080)).castAdd 2) = saved j.succ from returnedMergeBank_inner _ _ _ j]
      exact frame j.succ)
  exact ⟨z,F,k+n,exec.seq ran,Nat.add_le_add paid bill,same.trans user,result⟩

theorem inheritedReturnMerge_exec {P U : Type} {N Q price : ℕ} (lane : Descriptor)
    (positive : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price) :
    let T := intervalSplitTapes
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (program : Pr (Empty ⊕ P) H Q prime U)
      (bank : Fin T ↪ Fin H), bank 0 = caller 0 ∧
    ∀ (target : ℤ → Fin (prime+4)) (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk caller S).L (embStk caller S).R →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let V := volume prime lane
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (142081*(8*V+10)+1+price)+(149*(V*142080)*(T+5)+6) ∧ z.user = u.user ∧
        RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output) (embStk bank F).L (embStk bank F).R := by
  intro T H caller
  let live := intervalOwners 142080
  obtain ⟨childBank,host,program,apart,run⟩ := runInheritedChild lane child live
  let saved := (mergeSaved 142080).trans caller
  let returned := (childReturnFan dst).trans childBank
  have separate (i j) : saved i ≠ returned j := (apart _ (mergeSaved_outside _ i) _).symm
  let bank := returnedMergeBank saved returned separate
  let merge : Pr (Empty ⊕ P) H Q prime U := embProg bank Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
  refine ⟨host,program.seq merge,bank,returnedMergeBank_target _ _ _,?_⟩
  intro target data u S split empty prepared V output word
  have rep := intervalOwners_ready target data (embStk caller S) split
  obtain ⟨v,D,k,_,exec,paid,user,_,owners,keep⟩ := run data u S rep empty prepared
  exact mergeAfterReturnedRows host program saved returned separate capacity positive target data output
    (embStk caller S) u S split ⟨v,D,k,exec,paid,user,owners,fun i =>
      keep (mergeSaved 142080 i) (mergeSaved_outside _ i)⟩


private theorem caller_ne_front {a t n : ℕ} (j : Fin t) (i : Fin a) :
    (j.natAdd a).castAdd n ≠ (i.castAdd t).castAdd n := by
  intro eq
  have h := congrArg Fin.val eq
  change a+j.val = i.val at h
  omega

private theorem caller_ne_private {a t n : ℕ} (j : Fin t) (i : Fin n) :
    (j.natAdd a).castAdd n ≠ i.natAdd (a+t) := by
  intro eq
  have h := congrArg Fin.val eq
  change a+j.val = a+t+i.val at h
  omega

private theorem splitEncoded_exec {H Q V : ℕ} {P U : Type}
    (host : P → Pr P H Q prime U) (caller : Fin intervalSplitTapes ↪ Fin H)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) (positive : 0 < V)
    (input : Fin (V*142080) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime) :
    let x := fun k => SparseRoleCircuit.encode (a := prime) (input k)
    let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    S.R (caller 0) = List.ofFn x → (∀ j, S.L (caller j) = []) →
    (∀ j, j ≠ 0 → S.R (caller j) = []) →
    ∃ v D t, Exec host (embProg caller Empty.elim split) (mk u S) t (mk v D) ∧
      v.user = u.user ∧ t ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 ∧
      RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (List.ofFn x))
        (fun r i => input (finProdFinEquiv (i,r)))) (embStk caller D).L (embStk caller D).R ∧
      ∀ j, (∀ i, caller i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro x split source left empty
  obtain ⟨v,D,t,user,paid,exec,rep⟩ := intervalSplit_exec (P := Empty) Empty.elim capacity positive x
    (embDn caller u) (embStk caller S) source left empty
  obtain ⟨a,E,placed,_,state,view,off⟩ := exec_emb (ι := Empty.elim) (body' := host)
    caller.injective (fun e => nomatch e) exec u rfl S rfl
  refine ⟨a,E,t,placed,state.trans user,paid,?_,off⟩
  rw [view]
  exact rep

/-- Start with the interleaved payload on the caller's target, run the recursive
child on its cyclic rows, and return the wide descriptor transpose on that target. -/
theorem inheritedInterval_exec {P U : Type} {N Q price : ℕ} (lane : Descriptor)
    (positive : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price) :
    let T := intervalSplitTapes
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (program : Pr (Empty ⊕ P) H Q prime U)
      (bank : Fin T ↪ Fin H), bank 0 = caller 0 ∧
    ∀ (input : Fin (volume prime wide) → ZMod 2) u S,
      let x := fun k : Fin (V*142080) => SparseRoleCircuit.encode (a := prime) (input (k.cast size))
      S.R (caller 0) = List.ofFn x → (∀ j, S.L (caller j) = []) →
      (∀ j, j ≠ 0 → S.R (caller j) = []) →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let y := fun k : Fin (V*142080) => Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) input (k.cast size)
      let rows := fun r (i : Fin V) => y (finProdFinEquiv (i,r))
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(T+5)+5)*(V*142080)+24 + ((142081*(8*V+10)+1+price)+(149*(V*142080)*(T+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord (fun _ => blank) 0
          (List.ofFn fun k => SparseRoleCircuit.encode (y k))) rows) (embStk bank F).L (embStk bank F).R := by
  intro T H caller V wide size
  obtain ⟨host,worker,bank,target,run⟩ := inheritedReturnMerge_exec lane positive capacity child
  let split : Pr Empty T Q prime U := intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
  refine ⟨host,(embProg caller Empty.elim split).seq worker,bank,target,?_⟩
  intro input u S x source left empty fresh prepared y rows
  let data := fun r (i : Fin V) => input ((finProdFinEquiv (i,r)).cast size)
  let original := putWord (fun _ => blank) 0 (List.ofFn x)
  obtain ⟨a,E,t,placed,user,paid,start,off⟩ := splitEncoded_exec host caller capacity positive
    (fun k => input (k.cast size)) u S source left empty
  obtain ⟨z,F,n,ran,bill,same,result⟩ := run original data a E start (fun i => by
    have frame := off ((i.castAdd T).castAdd N) (fun j => caller_ne_front j i)
    exact ⟨frame.1.trans (fresh i).1,frame.2.trans (fresh i).2⟩) (fun i => by
    have frame := off (i.natAdd (142082+T)) (fun j => caller_ne_private j i)
    exact ⟨frame.1.trans (prepared i).1,frame.2.trans (prepared i).2⟩)
  have changed : (fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) = rows := by
    funext r i
    exact (transpose_trailingRows lane 142080 input i r).symm
  rw [changed] at result
  have merged (k : Fin (V*142080)) : rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 = y k := by
    exact congrArg y (finProdFinEquiv.apply_symm_apply k)
  simp only [merged] at result
  have overwrite : putWord original 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) =
      putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) :=
    FlatControlledShiftArray.overwrite _ _ _ _ (by simp)
  rw [overwrite] at result
  exact ⟨z,F,t+n,placed.seq ran,Nat.add_le_add paid bill,same.trans user,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
