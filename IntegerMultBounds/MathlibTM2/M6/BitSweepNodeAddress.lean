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

end IntegerMultBounds.MathlibTM2.M6.BitNode
