import IntegerMultBounds.Machine.CompactNativeRoleReservedBridge
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid

/-! Every complete corrected role family has a unique original row-major
array. This reverses the actual cyclic split, so final contraction and merge
can consume arbitrary completed role arrays without assuming a common source. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleRecombine
noncomputable section
open ButterflyStreamData (Coefficient)
open RecursiveInterchangeRows (pack)
open CompactGadgetReservationShape (Shape)

def collect {n c L : ℕ} (data : Fin c → Fin (n*L) → Coefficient) :
    CompactNativeRoleGeometry.Array n c L := fun z =>
  let ik := finProdFinEquiv.symm z
  let ij := finProdFinEquiv.symm ik.1
  data ij.2 (pack ij.1 ik.2)

theorem role_collect {n c L : ℕ} (data : Fin c → Fin (n*L) → Coefficient) (j : Fin c) :
    CompactNativeRoleGeometry.role (collect data) j=data j := by
  funext z
  simp only [CompactNativeRoleGeometry.role,collect,pack,Equiv.symm_apply_apply]
  exact congrArg (data j) (Equiv.apply_symm_apply finProdFinEquiv z)

theorem collect_role {n c L : ℕ} (f : CompactNativeRoleGeometry.Array n c L) :
    collect (CompactNativeRoleGeometry.role f)=f := by
  funext z
  simp only [collect,CompactNativeRoleGeometry.role,pack,Equiv.symm_apply_apply]
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]

def recombine (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell) :
    CompactSpectatorVisitGeometry.Array sh rows ell := fun z =>
  collect data (Fin.cast
    (CompactNativeRoleReservedBridge.grouped_cardinality rows c (CompactNativeRoleOriginal.inner sh ell) hd).symm z)

private theorem grouped_recombine (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell) :
    CompactNativeRoleReservedBridge.grouped sh rows c ell hd (recombine sh rows c ell hd data)=
      collect data := by
  funext z
  unfold CompactNativeRoleReservedBridge.grouped recombine
  exact congrArg (collect data) (Fin.ext rfl)

/-- Every original role is recovered exactly, at its unchanged inner coordinate. -/
theorem role_recombine (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell) (j : Fin c) :
    CompactNativeRoleReservedBridge.role sh rows c ell hd (recombine sh rows c ell hd data) j=data j := by
  unfold CompactNativeRoleReservedBridge.role
  rw [grouped_recombine,role_collect]

/-- Recombination loses neither row information nor coefficient bits. -/
theorem recombine_role (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    recombine sh rows c ell hd (CompactNativeRoleReservedBridge.role sh rows c ell hd f)=f := by
  unfold recombine CompactNativeRoleReservedBridge.role
  funext z
  have he := congrFun (collect_role
    (CompactNativeRoleReservedBridge.grouped sh rows c ell hd f))
    (Fin.cast (CompactNativeRoleReservedBridge.grouped_cardinality rows c
      (CompactNativeRoleOriginal.inner sh ell) hd).symm z)
  change _ = f z at he
  exact he

/-- Literal completed role payload is exactly the split representation of
its recombined whole array, with vacant master and restored role heads. -/
theorem rolePayload (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell) :
    CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd (recombine sh rows c ell hd data)=
      CyclicRowCopy.payload (fun _ => blank)
        (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data j))) 0 (fun _ => 0) := by
  unfold CompactNativeRoleReservedBridge.rolePayload
  simp_rw [role_recombine]

/-- Complete named-role endpoints determine a unique original whole array. -/
theorem role_ext (sh : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f g : CompactSpectatorVisitGeometry.Array sh rows ell)
    (he : ∀ j,CompactNativeRoleReservedBridge.role sh rows c ell hd f j=
      CompactNativeRoleReservedBridge.role sh rows c ell hd g j) : f=g := by
  have h : CompactNativeRoleReservedBridge.role sh rows c ell hd f=
      CompactNativeRoleReservedBridge.role sh rows c ell hd g := funext he
  have h' := congrArg (recombine sh rows c ell hd) h
  simpa only [recombine_role] using h'

theorem width (sh : Shape) (rows c ell w : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    ∀ i,(recombine sh rows c ell hd data i).1.length=w ∧
      (recombine sh rows c ell hd data i).2.length=w := fun _ => hw _ _

/-- A common actual role grid becomes the original whole-array grid needed
by the completed node's exact contraction and merge. -/
theorem grid (sh : Shape) (rows c ell q current M : ℕ) (hd : c ∣ rows)
    (data : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hg : ∀ j,CompactSpectatorInheritedGrid.Grid sh (rows/c) ell q current M (data j)) :
    CompactSpectatorInheritedGrid.Grid sh rows ell q current M (recombine sh rows c ell hd data) :=
  fun _ => hg _ _

end
end IntegerMultBounds.Machine.CompactNativeRoleRecombine
