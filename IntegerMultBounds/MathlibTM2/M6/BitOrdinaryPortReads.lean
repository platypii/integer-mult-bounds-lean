module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScan

/-! Physical directory rows at the labels selected by a checked PR589 port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback
open Shared50ModularControl (prime)
open IntegerMultBounds.Swap.Modular Matrix LabelTraversal FlatCoordinateLayout

/-- The packed row at each routed label implements the port's residual projector. -/
def PortReads {w : ℕ} (R W parents : ℕ) (interval : ℕ × ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (word output : Fin (R*((prime^(w+1))^128*W)) → ZMod 2) : Prop :=
  let N := (prime^(w+1))^128*W
  let M := prime^(w+1)
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  let box := M^(64*64)
  ∀ (c : Certificates.PR589.Nine.PortCertificate), c.Checked → ∀ block < parents,
        ∀ (g : LabelPadding.Label 64 (w+1)), IsUnit g →
        let chart := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
        let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
        let j := block*box+(LabelAddress.address (g*chart)).val
        ∀ x k, ownerRow (R := R) (N := N) rfl output j
          (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
            ownerRow (R := R) (N := N) rfl word j (index x k)

/-- The same directory row law serves every port certificate for the interval. -/
theorem PortReads.of_rows {w R W parents : ℕ} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))}
    {word output : Fin (R*((prime^(w+1))^128*W)) → ZMod 2}
    (records : R = parents*(prime^(w+1))^(64*64)) (upper : interval.2 ≤ 63) :
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    (∀ j : Fin R, if LabelStock.live 64 (w+1) 1 j then ∀ x k,
      ownerRow rfl output j (index ((projectorResidual finSumFinEquiv (reduce M D)
        parent (fun i => Ring.inverse (parent i)) (physicalLabel 64 (w+1) j)).mulVec x) k) =
        ownerRow rfl word j (index x k) else ownerRow rfl word j = ownerRow rfl output j) →
    PortReads R W parents interval parent word output := by
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  intro M D action
  unfold PortReads
  intro _ _ _ c checked block inside g unit chart P j
  have pos : j < R := by
    rw [records]
    exact (Nat.add_lt_add_left (LabelAddress.address (g*chart)).isLt _).trans_le
      ((Nat.succ_mul ..) ▸ Nat.mul_le_mul_right _ inside)
  apply ownerRow_projected rfl rfl word output c checked interval.1 interval.2 upper block g unit parent
    (fun i => Ring.inverse (parent i))
  simpa only [Fin.cast_refl,id_eq] using action ⟨j,pos⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
