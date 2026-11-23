module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitReturn

/-! Prepare the inverse permutation's dimensions and archive independently of its owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Right-stack words read by the return sweep. -/
noncomputable def returnSlotWord (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (i : Fin 66) :
    List (Fin (prime+4)) :=
  let M := prime^(w+1)
  let marks (n : ℕ) := List.replicate n (separator : Fin (prime+4))
  match i.val with
    | 10 => marks (w+1)
    | 18 => marks H
    | 29 => marks 1
    | 37 => marks M.size
    | 38 => (List.ofFn fun j => binSyms M.size (parent j).val).flatten
    | 53 => marks W
    | 63 => marks (M^112*W)
    | 65 => marks (B*(M^112*W))
    | _ => []

noncomputable def returnFileWord (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    File → List (Fin (prime+4))
  | .work i => returnSlotWord w H W B parent i
  | _ => []

noncomputable def returnSeed (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :=
  returnFileWord w H W B parent ∘ (Fintype.equivFin File).symm

theorem returnSeed_ready (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    let R := returnSeed w H W B parent
    ReturnHeaders w H parent W B R ∧ ∀ i, R (owners i) = [] := by
  intro R
  let M := prime^(w+1)
  let marks (n : ℕ) := List.replicate n (separator : Fin (prime+4))
  let slots := returnSlotWord w H W B parent
  let file := returnFileWord w H W B parent
  let e := Fintype.equivFin File
  have atReg (r : File) : R (e r) = file r := congrArg file (e.symm_apply_apply r)
  have atP (i : Fin 39) : R (p i) = slots (i.castLE (by decide)) := atReg _
  have atWork (i : Fin 66) : R (work i) = slots i := atReg _
  refine ⟨?_,fun i => atReg (.owner i)⟩
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

theorem returnHeaders_exists (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    ∃ R, ReturnHeaders w H parent W B R ∧ ∀ i, R (owners i) = [] :=
  ⟨returnSeed w H W B parent,returnSeed_ready w H W B parent⟩

/-- Only eight of the 66 work slots require a persistent seed word. -/
def returnSeedSlots : Fin 8 → Fin 66 := ![10,18,29,37,38,53,63,65]

theorem returnSlotWord_empty (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (i : Fin 66)
    (away : ∀ j, returnSeedSlots j ≠ i) : returnSlotWord w H W B parent i = [] := by
  unfold returnSlotWord
  split <;> first | rfl | exfalso
  all_goals first
    | exact away 0 (Fin.ext (by assumption)).symm
    | exact away 1 (Fin.ext (by assumption)).symm
    | exact away 2 (Fin.ext (by assumption)).symm
    | exact away 3 (Fin.ext (by assumption)).symm
    | exact away 4 (Fin.ext (by assumption)).symm
    | exact away 5 (Fin.ext (by assumption)).symm
    | exact away 6 (Fin.ext (by assumption)).symm
    | exact away 7 (Fin.ext (by assumption)).symm

theorem returnSeedLength (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    let M := prime^(w+1)
    (∑ j, (returnSlotWord w H W B parent (returnSeedSlots j)).length) =
      (w+1)+H+1+65*M.size+W+M^112*W+B*(M^112*W) := by
  intro M
  simp [Fin.sum_univ_succ,returnSeedSlots,returnSlotWord,length_binSyms,M]
  omega

/-- At the packed stage, copying and clearing the return words costs linear node volume. -/
theorem returnSeed_copyCost_le (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (hW : 0 < W) (height : H ≤ (prime^(w+1))^128+1) :
    (∑ j, (8*(returnSlotWord w H W 1 parent (returnSeedSlots j)).length+6))+1 ≤
      625*((prime^(w+1))^128*W) := by
  let M := prime^(w+1)
  let V := M^128*W
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have box : M^128 ≤ V := Nat.le_mul_of_pos_right _ hW
  have modulus : M ≤ V := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans box
  have atom : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans modulus
  have digits := (Nat.size_le.mpr Nat.lt_two_pow_self : M.size ≤ M).trans modulus
  have width : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos pos _)
  have tail : M^112*W ≤ V := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right pos (by decide : 112 ≤ 128))
  have hH : H ≤ V+1 := height.trans (Nat.succ_le_succ box)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, returnSeedLength]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,one_mul]
  change 8*((w+1)+H+1+65*M.size+W+M^112*W+M^112*W)+8*6+1 ≤ 625*V
  omega

noncomputable def packedStageStacks {N : ℕ} (seed : Stacks N prime)
    (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) : Stacks (size 0 N) prime :=
  let R := returnSeed w H W 1 parent
  let e := Fintype.equivFin (Register 0 N)
  let left : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.L j
    | _ => []
  let right : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.R j
    | .sweep j => R j
    | _ => []
  ⟨seed.inp,seed.out,left ∘ e.symm,right ∘ e.symm⟩

theorem packedStageStacks_sweep {N : ℕ} (seed : Stacks N prime)
    (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (r : File) :
    let j := sweep 0 N (Fintype.equivFin File r)
    (packedStageStacks seed w H W parent).R j = returnFileWord w H W 1 parent r := by
  simp [packedStageStacks,sweep,place,returnSeed,Function.comp_def]
  exact congrArg (returnFileWord w H W 1 parent) ((Fintype.equivFin File).symm_apply_apply r)

theorem packedStageStacks_returnCost {N : ℕ} (seed : Stacks N prime)
    (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (hW : 0 < W) (height : H ≤ (prime^(w+1))^128+1) :
    let prepared := packedStageStacks seed w H W parent
    (∑ j, (8*(prepared.R (sweep 0 N (work (returnSeedSlots j)))).length+6))+1 ≤
      625*((prime^(w+1))^128*W) := by
  intro prepared
  have word (j : Fin 8) : prepared.R (sweep 0 N (work (returnSeedSlots j))) =
      returnSlotWord w H W 1 parent (returnSeedSlots j) :=
    packedStageStacks_sweep seed w H W parent (.work _)
  simp only [word]
  exact returnSeed_copyCost_le w H W parent hW height

/-- A single private seed supplies the chart worker, the return file and
the temporary tape. Only the worker's live fan can vary at stage entry. -/
theorem packedStageSeed {N : ℕ} (fan : Fin (142081+2) ↪ Fin N) (seed : Stacks N prime)
    (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) :
    let place := chart 0 N
    let back := sweep 0 N
    let prepared := packedStageStacks seed w H W parent
    ∀ S : Stacks (size 0 N) prime,
      (∀ j, (∀ i, place (fan i) ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ReturnHeaders w H parent W 1 (embStk back S).R ∧
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) ∧
      S.L (tmp 0 N) = [] ∧ S.R (tmp 0 N) = [] ∧
      ∀ i, S.L (back (owners i)) = [] ∧ S.R (back (owners i)) = [] := by
  intro place back
  let R := returnSeed w H W 1 parent
  obtain ⟨headers,empty⟩ := returnSeed_ready w H W 1 parent
  let e := Fintype.equivFin (Register 0 N)
  let left : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.L j
    | _ => []
  let right : Register 0 N → List (Fin (prime+4))
    | .chart j => seed.R j
    | .sweep j => R j
    | _ => []
  intro prepared S fresh
  have atReg r (off : ∀ i, place (fan i) ≠ e r) : S.L (e r) = left r ∧ S.R (e r) = right r :=
    ⟨(fresh _ off).1.trans (congrArg left (e.symm_apply_apply r)),
      (fresh _ off).2.trans (congrArg right (e.symm_apply_apply r))⟩
  have bank j := atReg (.sweep j) (fun i => e.injective.ne (by intro eq; cases eq))
  have scratch := atReg (.crop 0) (fun i => e.injective.ne (by intro eq; cases eq))
  have view : (embStk back S).R = R := funext fun j => (bank j).2
  exact ⟨view ▸ headers,fun j off => atReg (.chart j) (fun i => place.injective.ne (off i)),
    scratch.1,scratch.2,fun i => ⟨(bank _).1,(bank _).2.trans (empty i)⟩⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
