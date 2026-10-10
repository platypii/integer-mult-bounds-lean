import IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedBank
import IntegerMultBounds.Machine.NativeEndpointCharacterSourceReady

/-! The complete actual uniform phase/negation boundary on the original recursive
caller bank, with parent-volume cost and all shared private storage reclaimed. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationSourceReady
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexEndpointRoleExchange (Wire)
variable {s w : ℕ} {sh : Shape}
attribute [local irreducible] NativeUniformPolynomialRotationNamedRoles.program

theorem leaf_capacity : 67≤CompactComplexSourceReadyWorkspace.leafTapes := by
  norm_num [CompactComplexSourceReadyWorkspace.leafTapes,CompactSpectatorLeafOriginal.tapes,
    CompactSpectatorLeafOriginal.localCount,ButterflySpectatorPorts.count]

def program (negative : Bool) :
    Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s roleCount+w) q 2 :=
  ⟨_,NativeEndpointSourceReadyPlacement.program leaf_capacity
    (NativeUniformPolynomialRotationNamedRoles.program (s:=10+s) (u:=9) (r:=67) negative (by omega)).2⟩

/-- All uniform correction prerequisites are constructed from the actual original raw
caller. The only borrowed leaf tapes are first67; every other private word is
retained, and the complete changed native payload is returned literally. -/
theorem runs (negative : Bool) (v : Stage sh) (parentRows ell p : ℕ)
    (hG : 0<sh.guard) (hA : 0<sh.axes)
    (hGK : sh.guard+1≤sh.chunk) (hpay : sh.payload=1)
    (hr : 0<parentRows/roleCount)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (before : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=NativePolynomialStageShape.width sh p ∧
      (before a i).2.length=NativePolynomialStageShape.width sh p)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (suffix : Tapes w 2)
    (hb : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt leaf_capacity⟩=(fun _ => blank)) :
    HoareTime (program (s:=s) (w:=w) negative).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead before)) frame leaf).append suffix)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead
            (NativeUniformPolynomialRotationNamedBank.data negative v before))) frame leaf).append suffix)
      (NativeUniformPolynomialRotationRoles.constant*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have hK : 0<sh.chunk := by omega
  have h := NativeUniformPolynomialRotationNamedRoles.runs_caller (r:=67) negative (by omega)
    v parentRows ell p hr hG hA hK hpay control queue scalar tail storage frame
    master masterHead before hw (SharedBank.empty 67 2) (by intro i; exact ⟨rfl,rfl⟩)
  dsimp only at h
  rw [NativeUniformPolynomialRotationNamedBank.caller_endpoint negative v parentRows ell
    control queue scalar (NativeEndpointCharacterPrepare.raw v parentRows ell p)
    tail storage frame master masterHead before] at h
  exact NativeEndpointSourceReadyPlacement.runs leaf_capacity _ _ frame leaf suffix hb h

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationSourceReady
