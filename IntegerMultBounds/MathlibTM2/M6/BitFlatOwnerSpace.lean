module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleOwner
public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhysicalStage

/-! Bound merge cleanup from the exact words handed back to the cyclic owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

/-- On the returned owner tapes the retained size is exactly the number
of output bits. Only the other tapes contribute a separate space charge. -/
theorem ParentStageWords.mergeCleanup_le {T m V D : ℕ} {port : Fin 142081 → Fin T}
    {fan : Fin (142081+2) ↪ Fin T} {x : Fin 142081 → Fin m → ZMod 2}
    {E F : Stacks T prime} (words : ParentStageWords port fan D x E)
    (owners : List (Fin 142081)) (others : List (Fin T)) :
    let bank := owners.map port ++ others
    (∀ j ∈ bank, (F.L j).length+(F.R j).length ≤ (E.L j).length+(E.R j).length+298*V) →
    (bank.map fun j => 4*(F.L j).length+2*(F.R j).length+4).sum ≤
      4*(owners.length*m+(others.map fun j => (E.L j).length+(E.R j).length).sum) +
        bank.length*(1192*V+4) := by
  intro bank growth
  have cells (i) : (E.L (port i)).length+(E.R (port i)).length = m := by
    rw [words.left,words.right,List.length_nil,List.length_ofFn,Nat.zero_add]
  have total : (bank.map fun j => (E.L j).length+(E.R j).length).sum =
      owners.length*m+(others.map fun j => (E.L j).length+(E.R j).length).sum := by
    simp only [bank,List.map_append,List.sum_append,List.map_map,Function.comp_def,cells,
      List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  exact total ▸ mergedOwnerCleanup_le bank E F V growth

/-- Preserving the non-owner tape lengths through the lane worker lets the
splitter's own entry bound pay for all remaining tapes after merge. -/
theorem ParentStageWords.splitMergeCleanup_le {T m V D : ℕ} {port : Fin 142081 → Fin T}
    {fan : Fin (142081+2) ↪ Fin T} {x : Fin 142081 → Fin m → ZMod 2}
    {S E F : Stacks T prime} (words : ParentStageWords port fan D x E)
    (owners : List (Fin 142081)) (others : List (Fin T))
    (entry : ∀ j, (S.L j).length+(S.R j).length ≤ 301*V+2)
    (restored : ∀ j ∈ others, (E.L j).length+(E.R j).length ≤ (S.L j).length+(S.R j).length) :
    let bank := owners.map port ++ others
    (∀ j ∈ bank, (F.L j).length+(F.R j).length ≤ (E.L j).length+(E.R j).length+298*V) →
    (bank.map fun j => 4*(F.L j).length+2*(F.R j).length+4).sum ≤
      4*(owners.length*m+others.length*(301*V+2))+bank.length*(1192*V+4) := by
  intro bank growth
  apply (words.mergeCleanup_le owners others growth).trans
  have bound (ls : List (Fin T)) (kept : ∀ j ∈ ls, (E.L j).length+(E.R j).length ≤ 301*V+2) :
      (ls.map fun j => (E.L j).length+(E.R j).length).sum ≤ ls.length*(301*V+2) := by
    induction ls with
    | nil => simp
    | cons j js ih =>
      rw [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      exact (Nat.add_le_add (kept j List.mem_cons_self) (ih (fun t h => kept t (List.mem_cons_of_mem _ h)))).trans_eq (Nat.add_comm ..)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.add_le_add_left
    (bound others (fun j hj => (restored j hj).trans (entry j))) _)) _

end IntegerMultBounds.MathlibTM2.M6.BitNode
