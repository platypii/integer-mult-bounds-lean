module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

/-! Merge the inherited recursive child's returned rows on the caller's target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

private def mergeSaved (c : ℕ) : Fin 3 ↪ Fin (((1+c)+2)+2) where
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
  have frame i := keep (mergeSaved 142080 i) (mergeSaved_outside _ i)
  obtain ⟨z,F,n,ran,bill,same,result,_,_⟩ := placedMergeReturnedOwners_exec host bank capacity positive
    target data output (embStk caller S) v D split (by
      rw [show (intervalOwners 142080).trans bank = returned from returnedMergeBank_owners _ _ _]
      exact owners) (by
      rw [show bank 0 = saved 0 from returnedMergeBank_target _ _ _]
      exact frame 0) (fun j => by
      dsimp only
      rw [show bank ((j.natAdd (1+142080)).castAdd 2) = saved j.succ from returnedMergeBank_inner _ _ _ j]
      exact frame j.succ)
  exact ⟨z,F,k+n,exec.seq ran,Nat.add_le_add paid bill,same.trans user,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
