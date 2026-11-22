module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRegisterFile
public import IntegerMultBounds.MathlibTM2.M6.BitSweepReturnAllOwners

/-! Return the encoded sweep result to node order on the same register file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Stack Host Node Routing CompactRows

def inverseSlot : Fin 8 ↪ Fin 66 := ⟨![54,55,56,57,29,58,50,7],by decide⟩
noncomputable def inv := inverseSlot.trans work

/-- Interpret an arbitrary stage result in node order. -/
noncomputable def nodeArray {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (y : OwnerArray w B W) : OwnerArray w B W :=
  let index := (Fintype.equivFin Role).trans (finCongr card_role)
  Fin.lastCases (y (Fin.last 142080)) fun j =>
    y j.castSucc ∘ nodeToSweep w B W parent units n (index.symm j)

theorem sweepArray_nodeArray {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (y : OwnerArray w B W) :
    sweepArray parent units n (nodeArray parent units n y) = y := by
  funext j i
  induction j using Fin.lastCases with
  | last => rfl
  | cast j =>
    simp only [sweepArray,nodeArray,Fin.lastCases_castSucc,Function.comp_apply,
      Equiv.apply_symm_apply]

theorem nodeArray_read {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (y : OwnerArray w B W) (b : Fin B) (j : Fin W) :
    readRoles (fun z => nodeWindowEquiv w B W parent units (b,windowState w z,j))
      (nodeArray parent units n y) = sweepRoles n b j y := by
  rw [← sweepArray_read, sweepArray_nodeArray]

/-- After the allocated route writes the node-order words, the same field
reversal returns every role to its flat physical address. -/
theorem nodeArray_flat {w W : ℕ} (n : Fin 9) (y : OwnerArray w 1 W)
    (flat : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2)
    (frame : ∀ r a, flat (sweepRoleTape r) a =
      nodeArray (fun _ => 1) (fun _ => isUnit_one) n y (sweepRoleTape r)
        (flatToNode w W (fun _ => 1) (fun _ => isUnit_one) a)) :
    ∀ r a, y (sweepRoleTape r) (flatToSweep w W n r a) = flat (sweepRoleTape r) a := by
  intro r a
  have roundTrip := congrFun (sweepArray_nodeArray (fun _ => 1) (fun _ => isUnit_one) n y) (sweepRoleTape r)
  rw [sweepArray_role] at roundTrip
  rw [← roundTrip,← flatToSweep_factor (fun _ => 1) (fun _ => isUnit_one)]
  simpa only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using (frame r a).symm

/-- Read a completed sweep through its allocated entry and return routes.
Only the common field-frame reads are needed at their outer boundaries. -/
theorem routedSweep_flat_read {w W : ℕ} (n : Fin 9)
    (input framed output : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2) (y : OwnerArray w 1 W)
    (entry : ∀ r a, M8.RevMachine.ext (framed (sweepRoleTape r))
      (flatToNode w W (fun _ => 1) (fun _ => isUnit_one) a).val = input (sweepRoleTape r) a)
    (back : ∀ r a, output (sweepRoleTape r) a =
      nodeArray (fun _ => 1) (fun _ => isUnit_one) n y (sweepRoleTape r)
        (flatToNode w W (fun _ => 1) (fun _ => isUnit_one) a)) :
    let words : OwnerArray w 1 W := fun t i => M8.RevMachine.ext (framed t) i.val
    let x := sweepArray (fun _ => 1) (fun _ => isUnit_one) n words
    ∀ j, sweepRoles n 0 j y = (Piece.stage n).run (sweepRoles n 0 j x) →
      let addr := fun z => flatWindowEquiv w W (windowState w z,j)
      readRoles addr output = (Piece.stage n).run (readRoles addr input) := by
  intro words x j sweep addr
  have first := sweepRoles_of_flat n input x (sweepArray_flat n input framed entry) j
  have last := sweepRoles_of_flat n output y (nodeArray_flat n y output back) j
  simpa only [addr,flatWindowEquiv_read] using last.symm.trans (sweep.trans (congrArg (Piece.stage n).run first))

theorem sweepAllocatedReturn_exec {P U : Type} {Q : ℕ} (body : P → Pr P tapes Q prime U)
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
      (∀ r, R (owners (sweepRoleTape r)) = List.ofFn (fun i => SparseRoleCircuit.encode (a := prime) (nodeArray parent units n x (sweepRoleTape r) i))) ∧
      ∀ j, (∀ r, owners (sweepRoleTape r) ≠ j) → R j = S.R j := by
  refine Exists.imp (fun program h => ?convert) (sweepReturnAllOwners_exec body p pool rankPool coordPool ?_ ?_ ?_ ?_
    rg g ?_ ?_ ?_ ?_ ?_ s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    owners bank ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ inv ?_ ?_ ?_ ?_ ?_ ?_ n)
  case convert =>
    obtain ⟨C,run⟩ := h
    refine ⟨C,?_⟩
    intro w H W B parent units tail M N labels fits width pos blocks x v S
      exponent bits unit size archive blank poolFree rankFree coordFree maskFree record empty fresh spare
    have free (i : Fin 8) (a : i ≠ 4) (b : i ≠ 7) : S.R (inv i) = [] := by
      fin_cases i <;> first | contradiction | exact empty |
        exact fresh 5 (by decide) | exact fresh 6 (by decide) | exact fresh 7 (by decide) |
        exact fresh 8 (by decide) | exact fresh 9 (by decide)
    have cells r i : nodeArray parent units n x (sweepRoleTape r)
        ((nodeToSweep (w+1) B W parent units n r).symm i) = x (sweepRoleTape r) i := by
      have h := congrFun (sweepArray_nodeArray parent units n x) (sweepRoleTape r)
      rw [sweepArray_role] at h
      exact congrFun h i
    simpa only [Function.comp_def, cells] using run w H W B parent units tail fits width pos blocks
      (fun r i => SparseRoleCircuit.encode (a := prime) (nodeArray parent units n x (sweepRoleTape r) i)) v S exponent bits unit size archive blank poolFree rankFree coordFree maskFree record empty fresh spare free
  all_goals intros
  all_goals try rfl
  all_goals simp [p, pool, rankPool, coordPool, rg, g, s, inv, bank, work, address_apply,
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
