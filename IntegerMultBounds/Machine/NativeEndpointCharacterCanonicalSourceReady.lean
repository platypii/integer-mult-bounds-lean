import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalNamedRoles
import IntegerMultBounds.Machine.NativeEndpointCharacterSourceReady
import IntegerMultBounds.Machine.NativeEndpointSourceReadyPlacement

/-! The complete actual source/sink character boundary on the original recursive
caller bank, with parent-volume cost and all shared private storage reclaimed. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalSourceReady
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open NativeEndpointCharacterRoles (arity)
open CompactComplexEndpointRoleExchange (Wire)
variable {s w : ℕ} {sh : Shape}
attribute [local irreducible] NativeEndpointCharacterCanonicalNamedRoles.program

abbrev leaf_capacity := NativeEndpointCharacterSourceReady.leaf_capacity

def program (sink : Bool) :
    Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s roleCount+w) q 2 :=
  ⟨_,NativeEndpointSourceReadyPlacement.program leaf_capacity
    (NativeEndpointCharacterCanonicalNamedRoles.program (s:=10+s) (u:=9) sink).2⟩

/-- All character prerequisites are constructed from the actual original raw
caller. The only borrowed leaf tapes are first67; every other private word is
retained, and the complete changed native payload is returned literally. -/
theorem runs (sink : Bool) (v : Stage sh) (parentRows ell p : ℕ)
    (hslots : v.slots=arity) (hG : 0<sh.guard) (hA : 0<sh.axes)
    (hGK : sh.guard+1≤sh.chunk) (hpay : sh.payload=1)
    (hr : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (before : Wire → Array sh (parentRows/CompactComplexScalarCountLifecycle.roleDivisor) ell)
    (hw : ∀ a i,(before a i).1.length=NativePolynomialStageShape.width sh p ∧
      (before a i).2.length=NativePolynomialStageShape.width sh p)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (suffix : Tapes w 2)
    (hb : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt leaf_capacity⟩=(fun _ => blank)) :
    HoareTime (program (s:=s) (w:=w) sink).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead before)) frame leaf).append suffix)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead
            (NativeEndpointCharacterNamedBank.data sink v hslots ell p before))) frame leaf).append suffix)
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have hK : 0<sh.chunk := by omega
  have h := NativeEndpointCharacterCanonicalNamedRoles.runs sink v parentRows ell p hslots hG hA hK hr
    control queue scalar tail storage frame master masterHead before hw
  dsimp only at h
  rw [NativeEndpointCharacterNamedBank.caller_endpoint sink v hslots ell p control queue scalar
    (CompactComplexNativeCodec.raw v parentRows ell p) tail storage frame master masterHead before] at h
  have ht := NativeEndpointCharacterCanonicalNamedRoles.time_linear (s:=10+s) (u:=9) v parentRows ell p
    hr hA hG hGK hpay
  have hh := h.consequence (fun _ h => h) (fun _ h => h) ht
  exact NativeEndpointSourceReadyPlacement.runs leaf_capacity _ _ frame leaf suffix hb hh

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalSourceReady
