module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitReturn

/-! Prepare the inverse permutation's dimensions and archive independently of its owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- The fixed sweep file admits all return headers simultaneously with blank owner destinations. -/
theorem returnHeaders_exists (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    ∃ R, ReturnHeaders w H parent W B R ∧ ∀ i, R (owners i) = [] := by
  let M := prime^(w+1)
  let marks (n : ℕ) := List.replicate n (separator : Fin (prime+4))
  let slots (i : Fin 66) : List (Fin (prime+4)) := match i.val with
    | 10 => marks (w+1)
    | 18 => marks H
    | 29 => marks 1
    | 37 => marks M.size
    | 38 => (List.ofFn fun j => binSyms M.size (parent j).val).flatten
    | 53 => marks W
    | 63 => marks (M^112*W)
    | 65 => marks (B*(M^112*W))
    | _ => []
  let file : File → List (Fin (prime+4))
    | .work i => slots i
    | _ => []
  let e := Fintype.equivFin File
  let R := file ∘ e.symm
  have atReg (r : File) : R (e r) = file r := congrArg file (e.symm_apply_apply r)
  have atP (i : Fin 39) : R (p i) = slots (i.castLE (by decide)) := atReg _
  have atWork (i : Fin 66) : R (work i) = slots i := atReg _
  refine ⟨R,?_,fun i => atReg (.owner i)⟩
  refine ⟨(congrArg List.length (atP 10)).trans List.length_replicate,
    (congrArg List.length (atP 18)).trans List.length_replicate,
    (congrArg List.length (atP 29)).trans List.length_replicate,
    (congrArg List.length (atP 37)).trans List.length_replicate,⟨[],by rw [List.append_nil]; exact atP 38⟩,?_,
    fun i => atReg (.matrixFrame i),fun i => atReg (.rankFrame i),fun i => atReg (.coordFrame i),?_,
    (congrArg List.length (atWork (gatherSlot 3))).trans List.length_replicate,atWork (gatherSlot 0),?_,?_,
    ⟨marks (M^112*W),marks (B*(M^112*W)),List.length_replicate,List.length_replicate,?_⟩⟩
  · intro i hi
    rw [atP]
    fin_cases i <;> first | rfl | contradiction
  · intro i hi
    change R (work (maskSlot i)) = []
    rw [atWork]
    cases i with
    | scratch j => fin_cases j <;> rfl
    | _ => rfl
  · intro i hi
    change R (work (gatherSlot i)) = []
    rw [atWork]
    fin_cases i <;> first | rfl | contradiction
  · intro i hi
    change R (work (scanSlot i)) = []
    rw [atWork]
    fin_cases i <;> rfl
  · intro r i hi
    change R (e (transReg r i)) = _
    rw [atReg,transReg,ite_eq_right hi]
    fin_cases i <;> rfl

/-- A single private seed supplies the chart worker, the return file and
the temporary tape. Only the worker's live fan can vary at stage entry. -/
theorem packedStageSeed {N : ℕ} (fan : Fin (142081+2) ↪ Fin N) (seed : Stacks N prime)
    (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    let place := chart 0 N
    let back := sweep 0 N
    ∃ prepared : Stacks (size 0 N) prime, ∀ S : Stacks (size 0 N) prime,
      (∀ j, (∀ i, place (fan i) ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ReturnHeaders w H parent W 1 (embStk back S).R ∧
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) ∧
      S.L (tmp 0 N) = [] ∧ S.R (tmp 0 N) = [] ∧
      ∀ i, S.L (back (owners i)) = [] ∧ S.R (back (owners i)) = [] := by
  intro place back
  obtain ⟨R,headers,empty⟩ := returnHeaders_exists w H W 1 parent
  let e := Fintype.equivFin (Register 0 N)
  let left : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.L j
    | _ => []
  let right : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.R j
    | .sweep j => R j
    | _ => []
  let prepared : Stacks (size 0 N) prime := ⟨seed.inp,seed.out,left ∘ e.symm,right ∘ e.symm⟩
  refine ⟨prepared,?_⟩
  intro S fresh
  have atReg r (off : ∀ i, place (fan i) ≠ e r) : S.L (e r) = left r ∧ S.R (e r) = right r :=
    ⟨(fresh _ off).1.trans (congrArg left (e.symm_apply_apply r)),
      (fresh _ off).2.trans (congrArg right (e.symm_apply_apply r))⟩
  have bank j := atReg (.sweep j) (fun i => e.injective.ne (by intro eq; cases eq))
  have scratch := atReg (.crop 0) (fun i => e.injective.ne (by intro eq; cases eq))
  have view : (embStk back S).R = R := funext fun j => (bank j).2
  exact ⟨view ▸ headers,fun j off => atReg (.chart j) (fun i => place.injective.ne (off i)),
    scratch.1,scratch.2,fun i => ⟨(bank _).1,(bank _).2.trans (empty i)⟩⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
