module

public import Mathlib.Logic.Equiv.Fin.Basic

/-! The layout change between a batch of replicas per core and a batch of cores
per replica. Offsets within encoded blocks are fixed. No ambient matrix coordinate
is rotated, and the equivalence covers empty dimensions without extra cases. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Swap the two batch indices, retaining every symbol's offset in its block. -/
def replicaBlockTranspose (M B W : ℕ) : Fin ((M*B)*W) ≃ Fin ((B*M)*W) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr
      (finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin M) (Fin B)).trans finProdFinEquiv))
      (Equiv.refl (Fin W))).trans finProdFinEquiv)

/-- A structural address, independent of which ordering a physical tape uses. -/
def replicaBlockAddress {M B W : ℕ} (core : Fin M) (replica : Fin B) (offset : Fin W) : Fin ((M*B)*W) :=
  finProdFinEquiv (finProdFinEquiv (core,replica),offset)

theorem replicaBlockAddress_val {M B W : ℕ} (core : Fin M) (replica : Fin B) (offset : Fin W) :
    (replicaBlockAddress core replica offset).val = (core.val*B+replica.val)*W+offset.val := by
  simp only [replicaBlockAddress,finProdFinEquiv_apply_val]
  simp only [Nat.mul_add,Nat.add_mul]
  ac_rfl

@[simp] theorem replicaBlockTranspose_address {M B W : ℕ}
    (core : Fin M) (replica : Fin B) (offset : Fin W) :
    replicaBlockTranspose M B W (replicaBlockAddress core replica offset) =
      replicaBlockAddress replica core offset := by
  simp [replicaBlockTranspose,replicaBlockAddress]

@[simp] theorem replicaBlockTranspose_symm_address {M B W : ℕ}
    (core : Fin M) (replica : Fin B) (offset : Fin W) :
    (replicaBlockTranspose M B W).symm (replicaBlockAddress replica core offset) =
      replicaBlockAddress core replica offset := by
  apply (replicaBlockTranspose M B W).injective
  simp

/-- The R4 grouped-profile formula realizes this transpose one replica at a
 time: group width W, stride B*W and replica-dependent base replica*W. -/
theorem replicaBlockAddress_groupedSource {M B W : ℕ}
    (core : Fin M) (replica : Fin B) (offset : Fin W) :
    (offset.val+W*core.val)/W*(B*W)+
        ((offset.val+W*core.val)%W+replica.val*W) =
      (replicaBlockAddress core replica offset).val := by
  have hW : 0 < W := lt_of_le_of_lt (Nat.zero_le _) offset.isLt
  rw [Nat.add_mul_div_left _ _ hW,Nat.div_eq_of_lt offset.isLt,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt offset.isLt]
  simp only [Nat.zero_add,replicaBlockAddress_val,Nat.add_mul]
  ac_rfl

theorem replicaBlockAddress_groupedSource_lt {M B W : ℕ}
    (core : Fin M) (replica : Fin B) (offset : Fin W) :
    (offset.val+W*core.val)/W*(B*W)+
      ((offset.val+W*core.val)%W+replica.val*W) < (M*B)*W := by
  rw [replicaBlockAddress_groupedSource]
  exact (replicaBlockAddress core replica offset).isLt

/-- The value-level operation specified to the routing layer. -/
def transposeReplicaBlocks {M B W : ℕ} {E : Type*} (values : Fin ((M*B)*W) → E) :
    Fin ((B*M)*W) → E := fun i => values ((replicaBlockTranspose M B W).symm i)

@[simp] theorem transposeReplicaBlocks_read {M B W : ℕ} {E : Type*}
    (values : Fin ((M*B)*W) → E) (core : Fin M) (replica : Fin B) (offset : Fin W) :
    transposeReplicaBlocks values (replicaBlockAddress replica core offset) =
      values (replicaBlockAddress core replica offset) := by
  simp [transposeReplicaBlocks]

/-- Reindexing is lossless: no values are padded, duplicated or discarded. -/
theorem transposeReplicaBlocks_injective {M B W : ℕ} {E : Type*} :
    Function.Injective (transposeReplicaBlocks (M := M) (B := B) (W := W) (E := E)) := by
  intro x y h
  funext i
  have he := congrFun h (replicaBlockTranspose M B W i)
  simpa only [transposeReplicaBlocks,Equiv.symm_apply_apply] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
