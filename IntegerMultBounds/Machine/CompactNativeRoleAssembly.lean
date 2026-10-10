import IntegerMultBounds.Machine.CompactNativeRoleOriginal

/-! Reassembly accepts arbitrary descendant results on the fixed role tapes,
not only the untouched input. Joining is a cardinality-preserving row-major
index definition, and the actual merge performs every payload transfer. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleAssembly
noncomputable section
open CompactNativeRoleGeometry (Array role)
open RecursiveInterchangeRows (pack)
open ButterflyStreamData (Coefficient)
open NativeZeroPaddingArray (word)
open CompactGadgetReservationShape (Shape)

def join {n c L : ℕ} (data : Fin c → Fin (n*L) → Coefficient) : Array n c L := fun z =>
  let rk := finProdFinEquiv.symm z
  let ij := finProdFinEquiv.symm rk.1
  data ij.2 (pack ij.1 rk.2)

theorem role_join {n c L : ℕ} (data : Fin c → Fin (n*L) → Coefficient) (j : Fin c) :
    role (join data) j=data j := by
  funext z
  simp [role,join,pack]
  change data j (finProdFinEquiv (finProdFinEquiv.symm z))=data j z
  rw [Equiv.apply_symm_apply]

theorem join_roles {n c L : ℕ} (f : Array n c L) : join (role f)=f := by
  funext z
  simp [join,role,pack]
  have hrow : finProdFinEquiv (z.divNat.divNat,z.divNat.modNat)=z.divNat := Equiv.apply_symm_apply _ _
  rw [hrow]
  change f (finProdFinEquiv (finProdFinEquiv.symm z))=f z
  rw [Equiv.apply_symm_apply]

theorem join_width {n c L : ℕ} (w : ℕ) (data : Fin c → Fin (n*L) → Coefficient)
    (hw : ∀ j z,(data j z).1.length=w ∧ (data j z).2.length=w) :
    ∀ z,(join data z).1.length=w ∧ (join data z).2.length=w := fun _ => hw _ _

def payload {n c L : ℕ} (data : Fin c → Fin (n*L) → Coefficient) :=
  CyclicRowCopy.payload (fun _ => blank) (fun j => NativeZeroPadding.word (word (data j))) 0 (fun _ => 0)

theorem merges (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (data : Fin c → Fin (n*CompactNativeRoleOriginal.inner s ell) → Coefficient)
    (hw : ∀ j z,(data j z).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (data j z).2.length=CompactNativeRoleHeaders.recordWidth s p) :
    HoareTime (CompactNativeRoleOriginal.mergeProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right source target) (payload (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data))
      (fun v => v=CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right source target)
        (CompactNativeRoleOriginal.sourcePayload (n:=n) (c:=c) s ell (join (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data)))
      (CompactNativeRoleOriginal.cost true n c s ell p rho left count slots right source target) := by
  have hh := CompactNativeRoleOriginal.merges n c s ell p rho left count slots right source target hc hn hG hA hK
    (join (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data)
      (join_width (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) _ data hw)
  simpa only [CompactNativeRoleOriginal.rolePayload,role_join,payload] using hh

end
end IntegerMultBounds.Machine.CompactNativeRoleAssembly
