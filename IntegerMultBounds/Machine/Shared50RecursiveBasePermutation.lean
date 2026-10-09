import IntegerMultBounds.Machine.RecursiveDigitRoleBank
import IntegerMultBounds.Machine.Shared50RecursiveCallReady

/-! The actual width-one digit machine produces precisely the same full-field
transpose as the recursive node contract, on arbitrary four-symbol payloads. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBasePermutation
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
variable {v : Descriptor}

private theorem width_modulus (hw : v.width = 1) : ActualAffineScaling.modulus v.width = prime := by
  simp only [ActualAffineScaling.modulus,hw,pow_one]

def outerAddress (a : RecursiveInterchangeScaling.Address v) : Fin (RecursiveDigitLayout.outer v) :=
  finProdFinEquiv (finProdFinEquiv (a.beforeRows,a.row),a.before)

/-- Packing the width-one digit view retains every spectator coordinate. -/
theorem digit_index (hw : v.width = 1) (a : RecursiveInterchangeScaling.Address v) :
    Fin.cast (RecursiveDigitLayout.split_volume v hw).symm
      (RecursiveDigitLayout.pack (outerAddress a) (Fin.cast (width_modulus hw) a.h) a.middle
        (Fin.cast (width_modulus hw) a.d) a.after) = RecursiveInterchangeScaling.index a := by
  apply Fin.ext
  rw [RecursiveInterchangeScaling.index_val]
  simp only [Fin.val_cast,RecursiveDigitLayout.pack,outerAddress,finProdFinEquiv,Equiv.coe_fn_mk,
    RecursiveInterchangeLayout.index,hw,pow_one]
  ring

theorem array_entry (hw : v.width = 1) (x : Fin (volume prime v) → Fin 4)
    (a : RecursiveInterchangeScaling.Address v) :
    RecursiveDigitRoleBank.array hw x
      (RecursiveInterchangeScaling.index (Shared50RecursiveNodeTranspose.swapAddress a)) =
      x (RecursiveInterchangeScaling.index a) := by
  have he := RecursiveDigitLayout.array_entry (q := prime) hw x (outerAddress a)
    (Fin.cast (width_modulus hw) a.h) a.middle (Fin.cast (width_modulus hw) a.d) a.after
  rw [digit_index hw a] at he
  have hs := digit_index hw (Shared50RecursiveNodeTranspose.swapAddress a)
  change Fin.cast _ (RecursiveDigitLayout.pack (outerAddress a) (Fin.cast _ a.d) a.middle
    (Fin.cast _ a.h) a.after) = _ at hs
  rw [hs] at he
  exact he

theorem array_transpose (hw : v.width = 1) (x : Fin (volume prime v) → Fin 4) :
    RecursiveDigitRoleBank.array hw x = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  funext z
  obtain ⟨a,rfl⟩ := RecursiveScalarIndex.scaling_surjective (v := v) z
  have hd := array_entry hw x (Shared50RecursiveNodeTranspose.swapAddress a)
  have ht := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd v.rows)
    x (Shared50RecursiveNodeTranspose.swapAddress a)
  have hi : Shared50RecursiveNodeTranspose.swapAddress (Shared50RecursiveNodeTranspose.swapAddress a) = a := rfl
  rw [hi] at hd ht
  exact hd.trans ht.symm

/-- The canonical recursive input has one physical input tape and blank World roles. -/
theorem source_roles (x : Fin (volume prime v) → Fin 4) :
    RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires x) =
      Shared50RecursiveCallSemantics.childRoles (RecursiveShiftRoleBank.source x) :=
  Shared50RecursiveCallReady.source_roles x

/-- Updating the common I/O tape is exactly the canonical output serialization. -/
theorem source_roles_updated (x out : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.updated
      (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires x))
      Shared50NodeSegments.io out =
      RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData Shared50RecursiveNodeLayout.wires out) := by
  rw [source_roles,source_roles]
  simp only [RecursiveShiftRoleBank.updated,Shared50RecursiveCallSemantics.childRoles,
    SharedPlacementAlphabet.setTape_setTape]

end
end IntegerMultBounds.Machine.Shared50RecursiveBasePermutation
