import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControls

/-! Source-only orientation retains all runtime stop descriptors and guard
scratch readiness on the original caller bank. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsFrame
noncomputable section
open Networks
open CompactComplexSourceReadyWorkspace (publicTapes bank leafTapes)
open SharedPlacementAlphabet (setTape)
variable {s c N : ℕ}

def source : Fin (publicTapes s c) := Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c))
def output (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s c) 2)
    (f : Fin N → ButterflyStreamData.Coefficient) :=
  if call.inverse then setTape v source (NativeZeroPadding.word
    (NativeZeroPaddingArray.word (NativePolynomialConjugationData.array f))) 0 else v

theorem node_output (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s c) 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2) (f : Fin N → ButterflyStreamData.Coefficient) :
    CompactComplexSourceReadyOrientation.output call (bank v leaf work) f=bank (output call v f) leaf work := by
  unfold CompactComplexSourceReadyOrientation.output output CompactComplexSourceReadyOrientation.source
    NativePolynomialConjugationWorkspace.source bank source
  split_ifs
  · rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]
  · rfl

theorem frame (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s c) 2)
    (f : Fin N → ButterflyStreamData.Coefficient) (i : Fin (publicTapes s c)) (hi : i≠source) :
    (output call v f).head i=v.head i ∧ (output call v f).tape i=v.tape i := by
  unfold output
  split_ifs <;> simp [setTape,hi]

theorem scratch_ne (i : Fin 10) : CompactComplexSourceReadyGuard.scratch (s:=s) (c:=c) i≠source := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [CompactComplexSourceReadyGuard.scratch,source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,Fin.val_castAdd,Fin.val_natAdd,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot] at hv
  split_ifs at hv
  · simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · simp only [Fin.val_natAdd] at hv
    unfold CompactComplexSourceReadyGuard.permanent CompactComplexNonleafRoleEntry.tapes
      CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
      CompactComplexControllerNativeFrame.tapes at hv
    omega

theorem dimension_ne : CompactComplexSourceReadyGuard.dimension (s:=s) (c:=c)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexSourceReadyGuard.dimension,source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem exponent_ne : CompactComplexSourceReadyGuard.exponent (s:=s) (c:=c)≠source := by
  intro he
  have hv := congrArg Fin.val he
  simp only [CompactComplexSourceReadyGuard.exponent,source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleChildBank.control,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_mk,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem ready (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s c) 2)
    (f : Fin N → ButterflyStreamData.Coefficient) (h : CompactComplexSourceReadyGuard.Ready v) :
    CompactComplexSourceReadyGuard.Ready (output call v f) := by
  intro i
  rw [(frame call v f _ (scratch_ne i)).1,(frame call v f _ (scratch_ne i)).2]
  exact h i

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsFrame
