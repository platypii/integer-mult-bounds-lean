import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit

/-! Actual current-row splitting retains the generated nonleaf target and
incoming live header. These are literal physical frame identities, so later
scalar and child events need not reconstruct a target from an advanced live. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafInitialFrame
noncomputable section
open CompactComplexSourceReadyWorkspace (publicTapes)
open CompactComplexSourceReadyNonleafTarget (targeted)
variable {s c : ℕ}

private theorem outside (j : Fin 10) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) i≠
      CompactComplexNonleafRoleChildBank.storage (Fin.castAdd s j) := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleSplit.slot,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

private theorem replace_outside {P U N a : ℕ} (e : Fin (P+U) ≃ Fin N)
    (v : Tapes N a) (w : Tapes P a) (port : Fin N)
    (h : ∀ i : Fin P,e (Fin.castAdd U i)≠port) :
    (Placement.replace e v w).head port=v.head port ∧
    (Placement.replace e v w).tape port=v.tape port := by
  obtain ⟨i,rfl⟩ := e.surjective port
  induction i using Fin.addCases (m:=P) (n:=U) with
  | left i => exact False.elim (h i rfl)
  | right i =>
    exact ⟨Placement.combine_head_extra _ _ _ _,Placement.combine_tape_extra _ _ _ _⟩

theorem storage_retained (v : Tapes (publicTapes s c) 2)
    (w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin 10) :
    let port := CompactComplexNonleafRoleChildBank.storage (Fin.castAdd s j)
    (Placement.replace CompactComplexNonleafRoleSplit.placement v w).head port=v.head port ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement v w).tape port=v.tape port := by
  apply replace_outside
  intro i
  simpa only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot] using outside j i

theorem target_retained (v : Tapes (publicTapes s c) 2) (n : ℕ)
    (w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement (targeted v n) w).head
      CompactComplexNonleafRoleChildBank.target=1 ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement (targeted v n) w).tape
      CompactComplexNonleafRoleChildBank.target=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n) := by
  have h := storage_retained (targeted v n) w (⟨8,by omega⟩ : Fin 10)
  have he : CompactComplexNonleafRoleChildBank.storage (s:=s) (c:=c)
      (Fin.castAdd s (⟨8,by omega⟩ : Fin 10))=CompactComplexNonleafRoleChildBank.target := by
    unfold CompactComplexNonleafRoleChildBank.target
    apply congrArg CompactComplexNonleafRoleChildBank.storage
    apply Fin.ext
    rfl
  dsimp only at h
  rw [he] at h
  exact ⟨h.1.trans (by simp [targeted,SharedPlacementAlphabet.setTape,CompactComplexNonleafRoleChildBank.target]),
    h.2.trans (by simp [targeted,SharedPlacementAlphabet.setTape,CompactComplexNonleafRoleChildBank.target])⟩

/-- The incoming live header survives target generation and current-row split. -/
theorem current_retained (v : Tapes (publicTapes s c) 2) (n : ℕ)
    (w : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement (targeted v n) w).head
      CompactComplexNonleafRoleChildBank.current=v.head CompactComplexNonleafRoleChildBank.current ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement (targeted v n) w).tape
      CompactComplexNonleafRoleChildBank.current=v.tape CompactComplexNonleafRoleChildBank.current := by
  have h := storage_retained (targeted v n) w (⟨7,by omega⟩ : Fin 10)
  have he : CompactComplexNonleafRoleChildBank.storage (s:=s) (c:=c)
      (Fin.castAdd s (⟨7,by omega⟩ : Fin 10))=CompactComplexNonleafRoleChildBank.current := by
    unfold CompactComplexNonleafRoleChildBank.current
    apply congrArg CompactComplexNonleafRoleChildBank.storage
    apply Fin.ext
    rfl
  dsimp only at h
  rw [he] at h
  have hne : CompactComplexNonleafRoleChildBank.current (s:=s) (c:=c)≠
      CompactComplexNonleafRoleChildBank.target := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,
      CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  exact ⟨h.1.trans (by simp [targeted,SharedPlacementAlphabet.setTape,Function.update_of_ne hne]),
    h.2.trans (by simp [targeted,SharedPlacementAlphabet.setTape,Function.update_of_ne hne])⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafInitialFrame
