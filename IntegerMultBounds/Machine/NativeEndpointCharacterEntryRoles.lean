import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalSourceReady
import IntegerMultBounds.Machine.CompactNativeRoleReservedBridge

/-! Current-row splitting produces precisely the original named role family
consumed by the canonical source character boundary. The fixed opaque role
divisor changes only cardinality casts, never serialized coefficient order. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterEntryRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexScalarCountLifecycle (roleDivisor roleDivisor_eq)
variable {sh : Shape}

theorem quotient (rows : ℕ) : rows/roleDivisor=rows/roleCount := by rw [roleDivisor_eq]
theorem cardinality (sh : Shape) (rows ell : ℕ) :
    rows/roleDivisor*(2^sh.bits*2^ell)=rows/roleCount*(2^sh.bits*2^ell) :=
  congrArg (fun r => r*(2^sh.bits*2^ell)) (quotient rows)

def data (rows ell : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell) :
    Wire → Array sh (rows/roleDivisor) ell :=
  fun a i => CompactNativeRoleReservedBridge.role sh rows roleCount ell hd f (roleEncoding a)
    (Fin.cast (cardinality sh rows ell) i)

private theorem word_cast {n m : ℕ} (h : n=m) (f : Fin m → ButterflyStreamData.Coefficient) :
    NativeZeroPaddingArray.word (fun i => f (Fin.cast h i))=NativeZeroPaddingArray.word f := by
  subst m
  rfl

theorem payload (rows ell : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell) :
    CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f=
      CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data rows ell hd f) := by
  have hw (j : Fin roleCount) : NativeZeroPaddingArray.word (data rows ell hd f (roleEncoding.symm j))=
      NativeZeroPaddingArray.word (CompactNativeRoleReservedBridge.role sh rows roleCount ell hd f j) := by
    unfold data
    rw [Equiv.apply_symm_apply]
    exact word_cast _ _
  unfold CompactNativeRoleReservedBridge.rolePayload CompactComplexEndpointRoleExchange.payload
  congr 1
  funext j
  rw [hw]

theorem width (rows ell p : ℕ) (hd : roleCount∣rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    ∀ a i,(data rows ell hd f a i).1.length=NativePolynomialStageShape.width sh p ∧
      (data rows ell hd f a i).2.length=NativePolynomialStageShape.width sh p := by
  intro a i
  exact hw _

theorem positive (rows : ℕ) (hr : 0<rows) (hd : roleCount∣rows) : 0<rows/roleDivisor := by
  rw [quotient]
  exact Nat.div_pos (Nat.le_of_dvd hr hd) (by norm_num [roleCount])

end
end IntegerMultBounds.Machine.NativeEndpointCharacterEntryRoles
