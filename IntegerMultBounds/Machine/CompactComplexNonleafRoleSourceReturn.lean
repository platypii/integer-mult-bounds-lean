import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrames

/-! Actual source-ready payload recovery on the permanent bank with seven
additional private tapes. The protected endpoints determine readiness; arbitrary
simultaneous controller changes and the private suffix supply their own frame. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturn
noncomputable section
open CompactComplexNonleafRoleEntry
open CompactGadgetReservationShape (Shape)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

abbrev tapes (s c : ℕ) := CompactComplexNonleafRoleEntry.tapes s c + 7

def base (v : Tapes (tapes s c) 2) : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2 :=
  ⟨fun i => v.head (Fin.castAdd 7 i), fun i => v.tape (Fin.castAdd 7 i)⟩
def tail (v : Tapes (tapes s c) 2) : Tapes 7 2 :=
  ⟨fun i => v.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i),
    fun i => v.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)⟩
theorem base_tail (v : Tapes (tapes s c) 2) : (base v).append (tail v) = v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp [base, tail]
  | right i => simp [base, tail]

def program (selected : Fin c) :=
  extend (CompactComplexNonleafRoleReturn.program (s:=s) selected) 7

def output (selected : Fin c) (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) : Tapes (tapes s c) 2 :=
  (CompactComplexNonleafRoleReturnFrames.framed
    (setTape v (roleTape selected) returned 0) (base u)).append (tail u)

private theorem source_numeric (i : Fin 43) : source (s:=s) (c:=c) ≠ numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [source,CompactComplexSpectatorTargetBank.numericSlot,numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_role (j : Fin c) : source (s:=s) (c:=c) ≠ roleTape j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [source,roleTape,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd,
    CompactComplexControllerNativeFrame.tapes] at hv
  omega

private theorem source_extra (i : Fin 2) :
    source (s:=s) (c:=c) ≠ Fin.natAdd (CompactComplexNativeCodecFrame.permanentTapes s c) i := by
  intro h
  have hv := congrArg Fin.val h
  have hs := (CompactComplexSpectatorTargetBank.numericSlot (s:=s) (c:=c) 65).isLt
  simp only [source,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c)
      (Fin.castAdd (CompactComplexNonleafRoleEntry.tapes s c-43) i) = numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

/-- Concrete restored numeric, source, vacant-role, stack and clock endpoints
identify the return input, without constraining any complementary controller. -/
theorem ready_eq (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (v u : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (returned : ℤ → Fin 6)
    (hheaders : Placement.active headerPlacement u = ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hsource : u.head source=0 ∧ u.tape source=returned)
    (hroles : ∀ j,u.head (roleTape j)=0 ∧ u.tape (roleTape j)=(fun _ => blank))
    (hstack : u.head stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head stack ∧
      u.tape stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape stack)
    (hclock : u.head clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head clock ∧
      u.tape clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape clock) :
    CompactComplexNonleafRoleReturnFrames.framed
      (setTape (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v)
        source returned 0) u = u := by
  have hh := (CompactComplexNonleafRoleEntry.output_headers selected sh rows ell p rho left count slots right src dst v).trans hheaders.symm
  have hn (i : Fin 43) := congrArg (fun z : Tapes 43 2 => (z.head i, z.tape i)) hh
  simp only [Placement.active,numeric_active] at hn
  have hs : ∀ i, CompactComplexNonleafRoleReturnFrames.Core i →
      (setTape (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v) source returned 0).head i=u.head i ∧
      (setTape (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v) source returned 0).tape i=u.tape i := by
    intro i hi
    rcases hi with ⟨j,rfl⟩ | rfl | ⟨j,rfl⟩ | rfl | rfl
    · simpa only [setTape,Function.update_of_ne (source_numeric j).symm] using
        (show _ ∧ _ from ⟨congrArg Prod.fst (hn j),congrArg Prod.snd (hn j)⟩)
    · simp only [setTape,Function.update_self]
      exact ⟨hsource.1.symm,hsource.2.symm⟩
    · have he := CompactComplexNonleafRoleEntry.output_roles_blank selected j sh rows ell p rho left count slots right src dst v
      simpa only [setTape,Function.update_of_ne (source_role j).symm] using
        ⟨he.1.trans (hroles j).1.symm,he.2.trans (hroles j).2.symm⟩
    · simp only [setTape,stack,Function.update_of_ne (source_extra (s:=s) (c:=c) 0).symm]
      exact ⟨hstack.1.symm,hstack.2.symm⟩
    · simp only [setTape,clock,Function.update_of_ne (source_extra (s:=s) (c:=c) 1).symm]
      exact ⟨hclock.1.symm,hclock.2.symm⟩
  exact CompactComplexNonleafRoleReturnFrames.framed_eq_of_core _ _
    (fun i hi => (hs i hi).1) (fun i hi => (hs i hi).2)

/-- Execute the genuine payload return directly from an actual restored raw
child-result bank, retaining its controller frame and arbitrary private suffix. -/
theorem runs (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true) v)
    (hreturned : RoleArrayStack.Supported returned
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hheaders : Placement.active headerPlacement (base u)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hresult : (base u).head source=0 ∧ (base u).tape source=returned)
    (hblank : ∀ j,(base u).head (roleTape j)=0 ∧ (base u).tape (roleTape j)=(fun _ => blank))
    (hstack : (base u).head stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head stack ∧
      (base u).tape stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape stack)
    (hclockFrame : (base u).head clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head clock ∧
      (base u).tape clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape clock) :
    HoareTime (program selected) (fun z => z=u)
      (fun z => z=output selected v u returned)
      (CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell p rho left count slots right src dst) := by
  have hready := ready_eq selected sh rows ell p rho left count slots right src dst v (base u) returned
    hheaders hresult hblank hstack hclockFrame
  have h := CompactComplexNonleafRoleReturnFrames.return_result selected sh rows ell p rho left count slots right src dst
    v (base u) returned hc hr hgroup hG hA hK hraw hclock hsource hroles hfree hreturned
  rw [hready] at h
  have he := hoare_extend_eq h (tail u)
  exact he.consequence (fun _ hz => hz.trans (base_tail u).symm) (fun _ hz => hz) le_rfl

theorem output_frame (selected : Fin c)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6)
    (i : Fin (CompactComplexNonleafRoleEntry.tapes s c))
    (hi : ¬ CompactComplexNonleafRoleReturnFrames.Core i) :
    (output selected v u returned).head (Fin.castAdd 7 i)=u.head (Fin.castAdd 7 i) ∧
    (output selected v u returned).tape (Fin.castAdd 7 i)=u.tape (Fin.castAdd 7 i) := by
  simpa only [output,Tapes.append,Fin.addCases_left,base] using
    CompactComplexNonleafRoleReturnFrames.framed_complement
      (setTape v (roleTape selected) returned 0) (base u) i hi

theorem output_extra (selected : Fin c)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) (i : Fin 7) :
    (output selected v u returned).head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
      u.head (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i) ∧
    (output selected v u returned).tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i)=
      u.tape (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes s c) i) := by
  simp [output,Tapes.append,tail]

/-- Protected return endpoints are exactly the original parent bank with the
selected arbitrary result installed. -/
theorem output_core (selected : Fin c)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6)
    (i : Fin (CompactComplexNonleafRoleEntry.tapes s c))
    (hi : CompactComplexNonleafRoleReturnFrames.Core i) :
    (output selected v u returned).head (Fin.castAdd 7 i)=
      (setTape v (roleTape selected) returned 0).head i ∧
    (output selected v u returned).tape (Fin.castAdd 7 i)=
      (setTape v (roleTape selected) returned 0).tape i := by
  simpa only [output,Tapes.append,Fin.addCases_left] using
    CompactComplexNonleafRoleReturnFrames.framed_core
      (setTape v (roleTape selected) returned 0) (base u) i hi

/-- The saved entry endpoint retains the original reusable clock. -/
theorem entry_clock (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head clock=v.head clock ∧
    (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape clock=v.tape clock := by
  apply CompactComplexNonleafRoleEntry.output_frame
  · intro j h
    have hv := congrArg Fin.val h
    have hj := (CompactComplexNativeCodecFrame.headerSlot (s:=s) (c:=c) j).isLt
    simp only [clock,numeric,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [clock,stack,Fin.val_natAdd,Fin.val_zero,Fin.val_one] at hv
    omega
  · exact (source_extra (s:=s) (c:=c) 1).symm
  · intro j h
    have hv := congrArg Fin.val h
    have hj := (CompactComplexSpectatorTargetBank.roleSlot (s:=s) j).isLt
    simp only [clock,roleTape,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturn
