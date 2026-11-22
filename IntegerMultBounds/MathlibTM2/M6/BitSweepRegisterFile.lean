module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepAllOwners

/-! Fixed register allocation for the PR589 stage permutation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Stack Host Node Routing CompactRows

inductive Register (matrix rank coord : ℕ) where
  | work (i : Fin 66)
  | matrixFrame (i : Fin matrix)
  | rankFrame (i : Fin rank)
  | coordFrame (i : Fin coord)
  | owner (i : Fin 142081)
  deriving DecidableEq, Fintype

abbrev File := Register ((sweepMatrixDepth+1)*13) ((sweepBinaryRankCode.depth+1)*13) ((sweepCoordDepth+1)*13)
noncomputable abbrev tapes := Fintype.card File

def gatherSlot : Fin 10 ↪ Fin 66 := ⟨![50,51,52,53,7,54,55,56,57,58],by decide⟩
def scanSlot : Fin 5 ↪ Fin 66 := ⟨![52,51,59,55,56],by decide⟩
def transposeSlot : Fin 8 ↪ Fin 66 := ⟨![52,60,61,62,63,64,0,65],by decide⟩

def maskSlot : BinaryMaskReg → Fin 66
  | .width => 35
  | .source => 46
  | .low => 47
  | .high => 48
  | .dst => 49
  | .scratch i => ⟨39+i.val,by omega⟩

theorem mask_inj : Function.Injective maskSlot := by
  intro i j h
  cases i <;> cases j <;> simp [maskSlot,Fin.ext_iff] at * <;> omega

noncomputable def address {ι : Type} (f : ι → File) (inj : Function.Injective f) : ι ↪ Fin tapes :=
  (⟨f,inj⟩ : ι ↪ File).trans (Fintype.equivFin File).toEmbedding

theorem address_apply {ι : Type} (f : ι → File) (inj : Function.Injective f) (i : ι) :
    address f inj i = Fintype.equivFin File (f i) := rfl

noncomputable def work := address Register.work (fun _ _ h => Register.work.inj h)
noncomputable def p : Fin 39 ↪ Fin tapes := (Fin.castLEEmb (show 39 ≤ 66 by decide)).trans work
noncomputable def pool := address Register.matrixFrame (fun _ _ h => Register.matrixFrame.inj h)
noncomputable def rankPool := address Register.rankFrame (fun _ _ h => Register.rankFrame.inj h)
noncomputable def coordPool := address Register.coordFrame (fun _ _ h => Register.coordFrame.inj h)
noncomputable def owners := address Register.owner (fun _ _ h => Register.owner.inj h)
noncomputable def rg := (⟨maskSlot,mask_inj⟩ : BinaryMaskReg ↪ Fin 66).trans work
noncomputable def g := gatherSlot.trans work
noncomputable def s := scanSlot.trans work

noncomputable def transReg (r : Role) (i : Fin 8) : File :=
  if i = 6 then .owner (sweepRoleTape r) else .work (transposeSlot i)

noncomputable def bank (r : Role) := address (transReg r) (by
  intro i j h
  by_cases a : i = 6 <;> by_cases b : j = 6 <;> simp_all [transReg,transposeSlot.injective.eq_iff])


/-- Carry each node word to its stage addresses, preserving the extra owner. -/
noncomputable def sweepArray {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (x : OwnerArray w B W) : OwnerArray w B W :=
  let index := (Fintype.equivFin Role).trans (finCongr card_role)
  Fin.lastCases (x (Fin.last 142080)) fun j =>
    x j.castSucc ∘ (nodeToSweep w B W parent units n (index.symm j)).symm

theorem sweepArray_role {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (x : OwnerArray w B W) (r : Role) :
    sweepArray parent units n x (sweepRoleTape r) =
      x (sweepRoleTape r) ∘ (nodeToSweep w B W parent units n r).symm := by
  let index := (Fintype.equivFin Role).trans (finCongr card_role)
  change sweepArray parent units n x (index r).castSucc = _
  unfold sweepArray
  simp only [Fin.lastCases_castSucc]
  change x (index r).castSucc ∘ (nodeToSweep w B W parent units n (index.symm (index r))).symm = _
  rw [index.symm_apply_apply]
  rfl

theorem sweepArray_read {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (x : OwnerArray w B W) (b : Fin B) (j : Fin W) :
    sweepRoles n b j (sweepArray parent units n x) =
      readRoles (fun z => nodeWindowEquiv w B W parent units (b,windowState w z,j)) x := by
  funext r z
  rw [nodeToSweep_read parent units]
  change sweepArray parent units n x (sweepRoleTape r) _ = _
  rw [sweepArray_role]
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rfl

/-- The owner array written by the allocated sweep route reads the original
flat word after the shared all-one frame conversion. -/
theorem sweepArray_flat {w W : ℕ} (n : Fin 9)
    (flat framed : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2)
    (frame : ∀ r a, M8.RevMachine.ext (framed (sweepRoleTape r))
      (flatToNode w W (fun _ => 1) (fun _ => isUnit_one) a).val = flat (sweepRoleTape r) a) :
    let words : OwnerArray w 1 W := fun t i => M8.RevMachine.ext (framed t) i.val
    ∀ r a, sweepArray (fun _ => 1) (fun _ => isUnit_one) n words (sweepRoleTape r)
      (flatToSweep w W n r a) = flat (sweepRoleTape r) a := by
  intro words r a
  rw [sweepArray_role,← flatToSweep_factor (fun _ => 1) (fun _ => isUnit_one)]
  simpa only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using frame r a

theorem sweepAllocatedOwners_exec {P U : Type} {Q : ℕ} (body : P → Pr P tapes Q prime U)
    (n : Fin 9) :
    ∃ (program : Pr P tapes Q prime U) (C : ℕ), ∀ (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))),
    let M := prime^(w+1)
    let N := M^128
    let labels := prime^(64*((w+1)*64))
    N < 2^H → H ≤ N+1 → 0 < W → 0 < B → ∀ (x : OwnerArray (w+1) B W), ∀ (v : HS tapes Q prime U) (S : Stacks tapes prime),
    (S.R (p 10)).length = w+1 → (S.R (p 18)).length = H → (S.R (p 29)).length = 1 →
    (S.R (p 37)).length = M.size → S.R (p 38) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail →
    (∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) → (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    (∀ j, j ≠ .width → S.R (rg j) = []) → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i → S.R (g i) = []) → (∀ i : Fin 5, i ≠ 0 → S.R (s i) = []) →
    ∀ (record row : List (Fin (prime+4))), record.length = M^112*W → row.length = B*(M^112*W) →
    (∀ r, embStk (bank r) S = transposeStacks (embStk (bank r) S) [] (List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (x (sweepRoleTape r) i))) [] record row) →
    ∃ z R t, z.user = v.user ∧ t ≤ 142080*(C*(M^16*(B*labels*(M^112*W)))+8)+1 ∧
      Exec body program (mk v S) t (mk z {S with R := R}) ∧
      (∀ r, R (owners (sweepRoleTape r)) = List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (sweepArray parent units n x (sweepRoleTape r) i))) ∧
      ∀ j, (∀ r, owners (sweepRoleTape r) ≠ j) → R j = S.R j := by
  refine Exists.imp (fun program h => ?convert) (sweepAllOwners_exec body p pool rankPool coordPool ?_ ?_ ?_ ?_
    rg g ?_ ?_ ?_ ?_ ?_ s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    owners bank ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ n)
  case convert =>
    obtain ⟨C,run⟩ := h
    refine ⟨C,?_⟩
    intro w H W B parent units tail M N labels fits width pos blocks x v S
    simpa only [sweepArray_role, Function.comp_def] using run w H W B parent units tail fits width pos blocks
      (fun r i => SparseRoleCircuit.encode (a := prime) (x (sweepRoleTape r) i)) v S
  all_goals intros
  all_goals try rfl
  all_goals simp [p, pool, rankPool, coordPool, rg, g, s, bank, work, address_apply,
    ne_eq, Function.Embedding.trans_apply, transReg, *]
  all_goals try dsimp [address]
  all_goals try simp only [Equiv.apply_eq_iff_eq, reduceCtorEq,
    not_false_eq_true, and_self]
  all_goals try split
  all_goals try simp only [reduceCtorEq, not_false_eq_true]
  all_goals try cases_type BinaryMaskReg
  all_goals try contradiction
  all_goals decide +revert

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile
