import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalRoles
import IntegerMultBounds.Machine.NativeEndpointCharacterNamedBank

/-! The actual original named sign loop uses private source/target normalization
and fixed early metadata. No runtime order parameter or ordering premise is supplied. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalNamedRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexEndpointRoleExchange (Address Wire tapes)
open NativeEndpointCharacterRoles (arity fixedWeights endpoints)
open NativeEndpointNamedPorts (focus)
open NativeEndpointCharacterNamedRoles (source role output coefficients source_injective source_focus)
variable {s u : ℕ} {sh : Shape}
attribute [local irreducible] NativeEndpointCharacterCanonicalRoles.program NativeEndpointCharacterCanonicalOriginal.cost

private theorem serialized_coefficients {rows ell : ℕ} (data : Wire → Array sh rows ell) (a : Wire) :
    UnitPhaseFullStreamNormalized.serialized (coefficients data a)=NativeZeroPaddingArray.word (data a) := by
  unfold UnitPhaseFullStreamNormalized.serialized NativeZeroPaddingArray.word coefficients
  congr 1
  exact (List.ofFn_congr (Nat.mul_assoc rows (2^sh.bits) (2^ell)).symm
    (fun i => ButterflyStreamData.encoded (data a i))).symm

def program (sink : Bool) := NativeEndpointCharacterCanonicalRoles.actualProgram
  (focus (s:=s) (u:=u)) (source sink)

theorem runs (sink : Bool) (v : Stage sh) (parentRows ell p : ℕ)
    (hslots : v.slots=arity) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hr : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (data : Wire → Array sh (parentRows/CompactComplexScalarCountLifecycle.roleDivisor) ell)
    (hw : ∀ a i,(data a i).1.length=NativePolynomialStageShape.width sh p ∧
      (data a i).2.length=NativePolynomialStageShape.width sh p) :
    let caller := (CompactComplexNativeCodecFrame.bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data)).append extra
    HoareTime (program (s:=s) (u:=u) sink).2
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(output sink v ell p data caller).append (FixedHeaderBankCopy.empty 67))
      (endpoints.length*(NativeEndpointCharacterCanonicalOriginal.cost (t:=tapes s u)
        CompactComplexScalarCountLifecycle.roleDivisor v parentRows ell p+1)) := by
  dsimp only
  apply NativeEndpointCharacterCanonicalRoles.runs focus (source sink) (source_injective sink) (source_focus sink)
    CompactComplexScalarCountLifecycle.roleDivisor (by rw [CompactComplexScalarCountLifecycle.roleDivisor_eq]; norm_num [CompactComplexRolePhaseSite.roleCount])
    v parentRows ell p arity fixedWeights NativeEndpointCharacterRoles.weights_length hslots
    hG hA hK hr (fun b => coefficients data (role sink b)) (fun b i => hw (role sink b) (Fin.cast (Nat.mul_assoc _ _ _) i)) endpoints
    NativeEndpointCharacterRoles.endpoints_nodup
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).2
    exact h.trans (by
      fin_cases i <;> rfl)
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).1
    exact h.trans (by
      fin_cases i <;> rfl)
  · intro b _
    simpa only [serialized_coefficients,NativeZeroPadding.word,source] using
      (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
        (CompactComplexNativeCodec.raw v parentRows ell p) tail storage extra master masterHead data
        (role sink b)).2
  · intro b _
    exact (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage extra master masterHead data
      (role sink b)).1

theorem time_linear (v : Stage sh) (parentRows ell p : ℕ)
    (hr : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) :
    endpoints.length*(NativeEndpointCharacterCanonicalOriginal.cost (t:=tapes s u)
      CompactComplexScalarCountLifecycle.roleDivisor v parentRows ell p+1)≤
      NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p :=
  NativeEndpointCharacterCanonicalRoles.time_linear _ _ _ _ _ hr hA hG hGK hpay

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalNamedRoles
