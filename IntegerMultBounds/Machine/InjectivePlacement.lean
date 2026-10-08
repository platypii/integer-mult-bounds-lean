import IntegerMultBounds.Machine.Placement
import Mathlib.Logic.Equiv.Fintype

/-! A fixed injection of active tape slots extends to a whole-bank placement.
The complementary tape ordering is irrelevant: every complementary tape and
head is preserved by the already verified placement construction. -/
namespace IntegerMultBounds.Machine.InjectivePlacement
variable {s u t : ℕ}

noncomputable def permutation (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) : Equiv.Perm (Fin t) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (fun i => (finCongr hsize) (Fin.castAdd u i)) slot
    ((finCongr hsize).injective.comp (Fin.castAdd_injective _ _)) hinj)

theorem permutation_apply (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (i : Fin s) :
    permutation slot hinj hsize ((finCongr hsize) (Fin.castAdd u i)) = slot i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (fun i => (finCongr hsize) (Fin.castAdd u i)) slot
    ((finCongr hsize).injective.comp (Fin.castAdd_injective _ _)) hinj) i

noncomputable def placement (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) : Fin (s+u) ≃ Fin t :=
  (finCongr hsize).trans (permutation slot hinj hsize)

@[simp] theorem active_slot (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (i : Fin s) : placement slot hinj hsize (Fin.castAdd u i) = slot i :=
  permutation_apply slot hinj hsize i

theorem active_bank {a : ℕ} (slot : Fin s → Fin t) (hinj : Function.Injective slot)
    (hsize : s+u = t) (v : Tapes t a) :
    Placement.active (placement slot hinj hsize) v = ⟨fun i => v.head (slot i),fun i => v.tape (slot i)⟩ := by
  simp [Placement.active]

end IntegerMultBounds.Machine.InjectivePlacement
