module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout

/-! Physical layout of a packed recursive payload at an arbitrary width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (index)
open Shared50ModularControl (prime)

def packedDescriptor (width W : ℕ) : Descriptor := ⟨1,1,1,width,1,W⟩

theorem packActive_packed (width W : ℕ) (i : Fin (volume prime (packedDescriptor width W))) :
    (CopyChildLayout.packActive (packedDescriptor width W) i).val = i.val := by
  obtain ⟨a,rfl⟩ := (CopyChildLayout.flatAddress (packedDescriptor width W)).surjective i
  change (CopyChildLayout.packActive _ (index a)).val = (index a).val
  rw [CopyChildLayout.packActive_index,RecursiveInterchangeScaling.index_val]
  have zero (k : Fin 1) : k.val = 0 := Nat.lt_one_iff.mp k.isLt
  change (a.after.val + W*(a.middle.val + 1*(a.before.val + 1*(a.row.val + 1*a.beforeRows.val)))) +
    (1*1*1*1*W)*(a.d.val + prime^width*a.h.val) = _
  simp only [RecursiveInterchangeLayout.index,packedDescriptor,zero,zero_mul,zero_add,
    mul_one,one_mul,add_zero]
  ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
