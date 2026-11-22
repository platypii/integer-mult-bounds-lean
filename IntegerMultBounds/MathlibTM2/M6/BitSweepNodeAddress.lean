module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepWindowRead

/-! Address permutations between a PR589 node and its corrected sweeps. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
open Cover Matrix Swap.Modular M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The node applies the parent weights on the first half and reverses the second half. -/
noncomputable def nodeDigitsEquiv (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) :
    Swap.Shear.State Axis (ZMod (prime^w)) ≃ (Fin 128 → ZMod (prime^w)) :=
  let R := M8.ReversedExchange.rev (R := ZMod (prime^w)) 64
  let F := fromBlocks (diagonal parent) 0 0 R
  let G := fromBlocks (diagonal (Ring.inverse ∘ parent)) 0 0 R
  let left := Weighted.diagonal_inv_mul (Ring.inverse ∘ parent) parent
    (fun i => Ring.inverse_mul_cancel _ (units i))
  let right := Weighted.diagonal_inv_mul parent (Ring.inverse ∘ parent)
    (fun i => Ring.mul_inverse_cancel _ (units i))
  let frame : Equiv.Perm ((Fin 64 ⊕ Fin 64) → ZMod (prime^w)) :=
    ⟨F.mulVec,G.mulVec,fun x => by
      simp [mulVec_mulVec,F,G,R,fromBlocks_multiply,left,M8.ReversedExchange.rev_mul_rev],
      fun x => by simp [mulVec_mulVec,F,G,R,fromBlocks_multiply,right,M8.ReversedExchange.rev_mul_rev]⟩
  let halves := (Equiv.sumArrowEquivProdArrow Axis Axis (ZMod (prime^w))).symm
  let axes := Equiv.arrowCongr (Equiv.sumCongr stageAxis stageAxis) (Equiv.refl (ZMod (prime^w)))
  let flat := Equiv.arrowCongr (@finSumFinEquiv 64 64) (Equiv.refl (ZMod (prime^w)))
  ((halves.trans axes).trans frame).trans flat

noncomputable def nodeWindowEquiv (w B W : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) :
    Fin B × (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W) ≃
      Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let digits := nodeDigitsEquiv w parent units
  ((Equiv.refl _).prodCongr (digits.prodCongr (Equiv.refl _))).trans (stagedCoordinateEquiv _ B W)

theorem nodeWindowEquiv_read {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (b : Fin B) (j : Fin W) (z : Axis ⊕ Axis → ℚ) :
    let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
    let v := addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm
    nodeWindowEquiv w B W parent units (b,windowState w z,j) =
      stagedOwnerIndex b (FlatCoordinateLayout.index ((frame.mulVec v) ∘ (@finSumFinEquiv 64 64).symm) j) := by
  intro frame v
  apply congrArg (fun x => stagedOwnerIndex b
    (FlatCoordinateLayout.index ((frame.mulVec x) ∘ (@finSumFinEquiv 64 64).symm) j))
  funext i
  cases i <;> rfl

/-- Reindex a node owner to read the corresponding sweep cell of a given role. -/
noncomputable def nodeToSweep (w B W : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role) :
    Equiv.Perm (Fin ((prime^w)^16*(B*((prime^w)^112*W)))) :=
  (nodeWindowEquiv w B W parent units).symm.trans (sweepRoleEquiv w B W n r)

theorem nodeToSweep_read {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (b : Fin B) (j : Fin W)
    (a : OwnerArray w B W) (r : Role) :
    sweepRoles n b j a r = readRoles (fun z => nodeToSweep w B W parent units n r
      (nodeWindowEquiv w B W parent units (b,windowState w z,j))) a r := by
  simpa only [nodeToSweep,Equiv.trans_apply,Equiv.symm_apply_apply] using sweepRoles_eq_read n b j a r

/-- Moving each role's cells along the node-to-sweep permutation makes its
sweep interpretation coincide with the ordinary node read at every point. -/
theorem sweepRoles_of_reindex {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (node sweep : OwnerArray w B W)
    (cells : ∀ (r : Role) i, let tape := bankTape r.bank (r.replica,r.port,r.cls)
      sweep tape (nodeToSweep w B W parent units n r i) = node tape i)
    (b : Fin B) (j : Fin W) :
    let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
    let addr := fun z => stagedOwnerIndex b (FlatCoordinateLayout.index
      ((frame.mulVec (addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm)) ∘
        (@finSumFinEquiv 64 64).symm) j)
    sweepRoles n b j sweep = readRoles addr node := by
  intro frame addr
  funext r z
  rw [nodeToSweep_read parent units]
  exact (cells r _).trans (congrArg (node (bankTape r.bank (r.replica,r.port,r.cls)))
    (nodeWindowEquiv_read parent units b j z))

/-- Encode the two unweighted parent fields in stage-axis order, followed by
the inherited spectator. This is the address used by the remainder windows. -/
noncomputable def flatWindowEquiv (w W : ℕ) :
    (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W) ≃ Fin ((prime^w)^128*W) :=
  let halves := (Equiv.sumArrowEquivProdArrow Axis Axis (ZMod (prime^w))).symm
  let axes := (Equiv.sumCongr stageAxis stageAxis).trans (@finSumFinEquiv 64 64)
  let digits := halves.trans (Equiv.arrowCongr axes (Equiv.refl _))
  ((digits.trans FlatCoordinateLayout.rankEquiv).prodCongr (Equiv.refl _)).trans finProdFinEquiv

theorem flatWindowEquiv_read {w W : ℕ} (z : Axis ⊕ Axis → ℚ) (j : Fin W) :
    flatWindowEquiv w W (windowState w z,j) = FlatCoordinateLayout.index
      ((addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) ∘
        (@finSumFinEquiv 64 64).symm) j := by
  apply congrArg (fun digits => FlatCoordinateLayout.index digits j)
  funext h
  change Sum.elim (windowState w z).1 (windowState w z).2
    ((Equiv.sumCongr stageAxis.symm stageAxis.symm) ((@finSumFinEquiv 64 64).symm h)) = _
  simp only [Function.comp_apply]
  cases (@finSumFinEquiv 64 64).symm h with
  | inl a => rfl
  | inr a => rfl

/-- Convert an inherited parent index into the active or inactive sweep
index for this role, retaining the same spectator in either case. -/
noncomputable def flatToSweep (w W : ℕ) (n : Fin 9) (r : Role) :
    Fin ((prime^w)^128*W) ≃ Fin ((prime^w)^16*(1*((prime^w)^112*W))) :=
  ((flatWindowEquiv w W).symm.trans (Equiv.uniqueProd _ (Fin 1)).symm).trans (sweepRoleEquiv w 1 W n r)

/-- The change from flat fields to the weighted node chart is shared by all
roles and stages. The existing node-to-sweep route supplies the second map. -/
noncomputable def flatToNode (w W : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) :
    Fin ((prime^w)^128*W) ≃ Fin ((prime^w)^16*(1*((prime^w)^112*W))) :=
  ((flatWindowEquiv w W).symm.trans (Equiv.uniqueProd _ (Fin 1)).symm).trans
    (nodeWindowEquiv w 1 W parent units)

theorem flatToNode_read {w W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (z : Axis ⊕ Axis → ℚ) (j : Fin W) :
    let v := addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
    flatToNode w W parent units (FlatCoordinateLayout.index (v ∘ (@finSumFinEquiv 64 64).symm) j) =
      stagedOwnerIndex (0 : Fin 1) (FlatCoordinateLayout.index ((frame.mulVec v) ∘ (@finSumFinEquiv 64 64).symm) j) := by
  intro v frame
  rw [← flatWindowEquiv_read]
  simp only [flatToNode,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact nodeWindowEquiv_read parent units 0 j z

/-- With all parent weights equal to one the shared frame reverses just
the second field. It is a fixed digit permutation at every precision. -/
def reverseSecondField : Equiv.Perm (Fin 128) :=
  (@finSumFinEquiv 64 64).symm.trans ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv)

private theorem staged_single_val {M W : ℕ} (i : Fin (M^128*W)) :
    (stagedOwnerIndex (0 : Fin 1) i).val = i.val := by
  let h := ordinaryCompact_width M W
  obtain ⟨⟨a,b⟩,split⟩ := finProdFinEquiv.surjective (i.cast h.symm)
  have value := congrArg Fin.val split
  simp only [Fin.val_cast,finProdFinEquiv_apply_val] at value
  simpa only [stagedOwnerIndex,← split,Equiv.symm_apply_apply,finProdFinEquiv_apply_val,
    Fin.val_zero,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.one_mul] using value

theorem flatToNode_unit_read {w W : ℕ} (z : Axis ⊕ Axis → ℚ) (j : Fin W) :
    let v := addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm
    let digits := v ∘ (@finSumFinEquiv 64 64).symm
    (flatToNode w W (fun _ => 1) (fun _ => isUnit_one) (FlatCoordinateLayout.index digits j)).val =
      (FlatCoordinateLayout.index (digits ∘ reverseSecondField) j).val := by
  intro v digits
  rw [flatToNode_read,staged_single_val]
  apply congrArg (fun x => (FlatCoordinateLayout.index x j).val)
  funext i
  simp only [digits,reverseSecondField,Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply,
    fromBlocks_mulVec,zero_mulVec,add_zero,zero_add,show (diagonal fun _ : Fin 64 => (1 : ZMod (prime^w))) = 1 from rfl,one_mulVec,Fallback.rev_mulVec]
  cases (@finSumFinEquiv 64 64).symm i <;> rfl

section
open Stack Host Fallback
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states

/-- From the prepared packing headers, change one owner from flat coordinates
to the all-one parent frame at the parent rate. The output words stay on the
same ports, and the other owners keep their data. -/
theorem flatToNode_unit_exec {k : ℕ} (owner : Fin k) (body : P → Pr P ((N+35)+k) Q prime U) :
    ∃ (code : Pr P ((N+35)+k) Q prime U) (C : ℝ), ∀ w W, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ (v : HS ((N+35)+k) Q prime U) (owners : Stacks k prime) (data : Fin k → Fin V → ZMod 2),
      (∀ i j, readAt blank (owners.L i) (owners.R i) j = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data i) j) →
      ∃ z F, ∃ time : ℕ, ∃ out : Fin V → ZMod 2,
        Exec body code (mk v (helperPackInput w W owners)) time (mk z F) ∧ z.user = v.user ∧
        (time : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        (∀ i : Fin k, ∀ j, readAt blank (F.L (i.natAdd (N+35))) (F.R (i.natAdd (N+35))) j =
          M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ Function.update data owner out i) j) ∧
        ∀ (x : Axis ⊕ Axis → ℚ) (j : Fin W),
          let a := flatWindowEquiv (w+1) W (windowState (w+1) x,j)
          ext out (flatToNode (w+1) W (fun _ => 1) (fun _ => isUnit_one) a).val = data owner a := by
  obtain ⟨code,C,run⟩ := ownerFieldPerm_exec owner reverseSecondField body
  refine ⟨code,C,?_⟩
  intro w W hW M V v owners data reads
  obtain ⟨ready,clean⟩ := helperPackInput_ready w W owners data reads
  obtain ⟨z,F,time,out,user,paid,exec,stored,_,act,_⟩ := run w W hW v _ [] (fun _ => blank) 0 data ready clean
  refine ⟨z,F,time,out,exec,user,paid,?_,?_⟩
  · intro i j
    have cell := (stored i).src j
    rw [show helperRecordBank i 24 = i.natAdd (N+35) from payloadPlacement_shared _ _,sub_zero] at cell
    exact cell
  · intro x j a
    dsimp only [a]
    rw [flatWindowEquiv_read,flatToNode_unit_read,ext_apply]
    exact act _ j

end

theorem flatToSweep_factor {w W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role) :
    (flatToNode w W parent units).trans (nodeToSweep w 1 W parent units n r) = flatToSweep w W n r := by
  ext i
  simp only [flatToNode,nodeToSweep,flatToSweep,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem sweepRoles_of_flat {w W : ℕ} (n : Fin 9)
    (flat : Fin 142081 → Fin ((prime^w)^128*W) → ZMod 2) (sweep : OwnerArray w 1 W)
    (cells : ∀ (r : Role) i, let tape := bankTape r.bank (r.replica,r.port,r.cls)
      sweep tape (flatToSweep w W n r i) = flat tape i) (j : Fin W) :
    let address := fun z => FlatCoordinateLayout.index
      ((addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) ∘
        (@finSumFinEquiv 64 64).symm) j
    sweepRoles n 0 j sweep = readRoles address flat := by
  intro address
  funext r z
  rw [sweepRoles_eq_read]
  have cell := cells r (flatWindowEquiv w W (windowState w z,j))
  simp only [flatToSweep,Equiv.trans_apply,Equiv.symm_apply_apply] at cell
  rw [flatWindowEquiv_read] at cell
  exact cell

/-- At both ends of a corrected sweep the role permutation gives the
logical stage read on the flat parent bank, simultaneously for all spectators. -/
theorem correctedSweep_flat [M8.Machine.Net] :
    ∃ (C : ℝ) (tapes states : ℕ), ∀ (n : Fin 9) (w W : ℕ), 0 < w → 0 < W →
      let M := prime^w
      let V := M^16*(1*(M^112*W))
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        enter.tapes ≤ tapes ∧ leave.tapes ≤ tapes ∧ enter.states ≤ states ∧ leave.states ≤ states ∧
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        ∀ (a d : Fin 142081 → Fin (M^128*W) → ZMod 2) x y,
          sweepEffect n w 1 W (enter.transform x) y →
          (∀ (r : Role) i, let tape := bankTape r.bank (r.replica,r.port,r.cls)
            x tape (flatToSweep w W n r i) = a tape i) →
          (∀ (r : Role) i, let tape := bankTape r.bank (r.replica,r.port,r.cls)
            leave.transform y tape (flatToSweep w W n r i) = d tape i) →
          ∀ j : Fin W,
            let address := fun z => FlatCoordinateLayout.index
              ((addressMod M z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) ∘ (@finSumFinEquiv 64 64).symm) j
            readRoles address d = (Piece.stage n).run (readRoles address a) := by
  obtain ⟨C,tapes,states,build⟩ := correctedSweep_read
  refine ⟨C,tapes,states,?_⟩
  intro n w W hw hW M V
  have hp := Shared50ModularControl.prime_prime.pos
  obtain ⟨enter,leave,et,lt,es,ls,cost,act⟩ := build n w 1 W hw (by positivity)
  refine ⟨enter,leave,et,lt,es,ls,cost,?_⟩
  intro a d x y step start finish j address
  exact (sweepRoles_of_flat n d (leave.transform y) finish j).symm.trans
    ((act x y step 0 j).trans (congrArg (Piece.stage n).run (sweepRoles_of_flat n a x start j)))

end IntegerMultBounds.MathlibTM2.M6.BitNode
