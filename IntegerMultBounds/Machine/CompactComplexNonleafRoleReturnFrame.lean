import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturn

/-! Parametric controller-frame preservation at the actual nonleaf payload
return. A child may advance an old permanent live-denominator slot while its
selected result remains at source65. The reverse generated-count boundary keeps
that advanced header and restores the original ancestor payload frame. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrame
noncomputable section
open CompactComplexNonleafRoleEntry
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c) (Fin.castAdd (tapes s c-43) i)=numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

private theorem frame_headers (i : Fin (tapes s c)) (hi : ∀ j,i≠numeric j)
    (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.active headerPlacement (setTape v i f p)=Placement.active headerPlacement v := by
  apply congrArg₂ Tapes.mk <;> funext j <;>
    simp only [numeric_active,setTape,Function.update_of_ne (hi j).symm]

/-- Unselected payload saves and the selected source move both frame this
controller update, regardless of its numerical contents or current head. -/
theorem parked_set_frame (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2)
    (i : Fin (tapes s c)) (f : ℤ → Fin 6) (p : ℤ)
    (hs : i≠stack) (hsource : i≠source) (hr : ∀ j,i≠roleTape j) :
    parked selected n (setTape v i f p)=setTape (parked selected n v) i f p := by
  unfold parked RoleArrayCall.entered
  rw [CompactComplexNonleafRoleReturn.saved_setTape layout (inactive selected) n v i f p hs
    (by intro r hmem;obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hmem).1;exact hr j)]
  have hselected := hr selected
  have hselected' := hselected.symm
  apply congrArg₂ Tapes.mk <;> funext j <;>
    by_cases hj : j=i <;> by_cases hsrc : j=source <;> by_cases hrole : j=roleTape selected <;>
    simp_all [RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,setTape]

/-- Literal generated entry endpoints commute with arbitrary retained
controller updates outside numeric/source/role payload and payload-stack slots. -/
theorem output_set_frame (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (i : Fin (tapes s c)) (f : ℤ → Fin 6) (p : ℤ)
    (hi : ∀ j,i≠numeric j) (hs : i≠stack) (hsource : i≠source) (hr : ∀ j,i≠roleTape j)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    output selected sh rows ell metadataP rho left count slots right src dst (setTape v i f p)=
      setTape (output selected sh rows ell metadataP rho left count slots right src dst v) i f p := by
  rw [CompactComplexNonleafRoleReturn.output_eq selected sh rows ell metadataP rho left count slots right src dst _
      ((frame_headers i hi v f p).trans hraw),
    CompactComplexNonleafRoleReturn.output_eq selected sh rows ell metadataP rho left count slots right src dst v hraw]
  rw [CompactComplexNonleafRoleReturn.saved_setTape layout [sourceRole] _ v i f p hs
    (by intro r hmem;simp only [List.mem_singleton] at hmem;subst r;exact hsource),
    parked_set_frame selected _ _ i f p hs hsource hr]

private theorem update_comm {t a : ℕ} (v : Tapes t a) (i j : Fin t) (hi : i≠j)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    setTape (setTape v i f p) j g q=setTape (setTape v j g q) i f p := by
  apply congrArg₂ Tapes.mk <;> funext k <;>
    by_cases hk : k=i <;> by_cases hj : k=j <;> simp_all [setTape]

/-- The genuine return keeps an arbitrary advanced controller word while it
recovers the selected result and the full saved parent/ancestor payload frame. -/
theorem return_result (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (returned : ℤ → Fin 6) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ)
    (hi : ∀ j,i≠numeric j) (hs : i≠stack) (hsourceSlot : i≠source)
    (hrslot : ∀ j,i≠roleTape j) (hclockSlot : i≠clock)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) v)
    (hreturned : RoleArrayStack.Supported returned
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true)) :
    HoareTime (CompactComplexNonleafRoleReturn.program selected)
      (fun z => z=setTape
        (setTape (output selected sh rows ell metadataP rho left count slots right src dst v) source returned 0)
        i advanced head)
      (fun z => z=setTape (setTape v (roleTape selected) returned 0) i advanced head)
      (CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell metadataP rho left count slots right src dst) := by
  let u := setTape v i advanced head
  have hraw' := (frame_headers i hi v advanced head).trans hraw
  have hclock' : u.head clock=0 ∧ u.tape clock=(fun _ => blank) := by
    simpa only [u,setTape,Function.update_of_ne hclockSlot.symm] using hclock
  have hsource' : u.head source=0 ∧ RoleArrayStack.Supported (u.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) := by
    simpa only [u,setTape,Function.update_of_ne hsourceSlot.symm] using hsource
  have hroles' (j : Fin c) : u.head (roleTape j)=0 ∧ RoleArrayStack.Supported (u.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) := by
    simpa only [u,setTape,Function.update_of_ne (hrslot j).symm] using hroles j
  have hfree' : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) u := by
    simpa only [CompactComplexNonleafRoleReturn.Free,u,setTape,Function.update_of_ne hs.symm] using hfree
  have h := CompactComplexNonleafRoleReturn.runs_result (s:=s) selected sh rows ell metadataP rho left count slots
    right src dst u returned hc hr hgroup hG hA hK hraw' hclock' hsource' hroles' hfree' hreturned
  dsimp only [u] at h
  rw [output_set_frame selected sh rows ell metadataP rho left count slots right src dst v i advanced head
    hi hs hsourceSlot hrslot hraw,
    update_comm _ i source hsourceSlot advanced returned head 0,
    update_comm _ i (roleTape selected) (hrslot selected) advanced returned head 0] at h
  exact h

/-- An existing permanent recursion-storage slot retains its physical index. -/
def oldSlot (j : Fin s) : Fin (tapes s c) :=
  Fin.castAdd 2 (CompactComplexSpectatorTargetBank.oldSlot (c:=c) j)

/-- Every old storage slot, including the genuine live7 denominator when it
exists, satisfies all exclusions needed for parametric physical return. -/
theorem old_slot_disjoint (j : Fin s) :
    (∀ k : Fin 43,oldSlot (c:=c) j≠numeric k) ∧
    oldSlot (c:=c) j≠stack ∧ oldSlot (c:=c) j≠source ∧
    (∀ k : Fin c,oldSlot (c:=c) j≠roleTape k) ∧ oldSlot (c:=c) j≠clock := by
  have hj := j.isLt
  constructor
  · intro k h
    have hk := k.isLt
    have hv := congrArg Fin.val h
    simp only [oldSlot,CompactComplexSpectatorTargetBank.oldSlot,numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.storageSlot,
      CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [oldSlot,CompactComplexSpectatorTargetBank.oldSlot,stack,
      CompactComplexNativeCodecFrame.permanentTapes,CompactComplexNativeRoleBridge.publicTapes,
      CompactComplexControllerNativeFrame.tapes,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [oldSlot,CompactComplexSpectatorTargetBank.oldSlot,source,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.storageSlot,
      CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  constructor
  · intro k h
    have hv := congrArg Fin.val h
    simp only [oldSlot,CompactComplexSpectatorTargetBank.oldSlot,roleTape,
      CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
      CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.tapes,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [oldSlot,CompactComplexSpectatorTargetBank.oldSlot,clock,
      CompactComplexNativeCodecFrame.permanentTapes,CompactComplexNativeRoleBridge.publicTapes,
      CompactComplexControllerNativeFrame.tapes,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrame
