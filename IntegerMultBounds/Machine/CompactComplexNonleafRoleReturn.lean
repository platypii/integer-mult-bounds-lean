import IntegerMultBounds.Machine.CompactComplexNonleafRoleEntry

/-! Actual reverse payload boundary on the same depth-independent bank as
NonleafRoleEntry. Both volume counts are regenerated from raw numeric geometry:
parent inactive arrays are popped before the retained master source, and every
generated word is erased. Child-result semantics and recursive execution remain
separate from this exact physical payload-frame recovery. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleReturn
noncomputable section
open CompactComplexNonleafRoleEntry
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

/-- Numeric replacement commutes with a physical payload update outside its
active bank. It never needs a blank frame or head-zero ancestor stack. -/
theorem replace_setTape {t n u a : ℕ} (e : Fin (n+u) ≃ Fin t) (v : Tapes t a)
    (small : Tapes n a) (i : Fin t) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hi : ∀ j,i≠e (Fin.castAdd u j)) :
    Placement.replace e (setTape v i f p) small=setTape (Placement.replace e v small) i f p := by
  apply congrArg₂ Tapes.mk <;> funext k
  all_goals
    obtain ⟨k,rfl⟩ := e.surjective k
    induction k using Fin.addCases with
    | left k =>
      simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape,(hi k).symm]
    | right k =>
      by_cases hk : e (Fin.natAdd n k)=i
      · subst i
        simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape]
      · simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape,hk]

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c) (Fin.castAdd (tapes s c-43) i)=numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

private theorem source_numeric (i : Fin 43) : source (s:=s) (c:=c)≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [source,CompactComplexSpectatorTargetBank.numericSlot,numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem stack_numeric (i : Fin 43) : stack (s:=s) (c:=c)≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := (CompactComplexNativeCodecFrame.headerSlot (s:=s) (c:=c) i).isLt
  simp only [stack,numeric,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem role_numeric (j : Fin c) (i : Fin 43) : roleTape (s:=s) j≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [roleTape,CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Numeric replacement commutes with parking any actual payload role. -/
theorem save_replace (r : RoleArrayFrames.Role (layout (s:=s) (c:=c)))
    (hr : ∀ j,r.val≠numeric j) (n : ℕ) (v : Tapes (tapes s c) 2) (small : Tapes 43 2) :
    RoleArrayFrames.saved layout [r] n (Placement.replace headerPlacement v small)=
      Placement.replace headerPlacement (RoleArrayFrames.saved layout [r] n v) small := by
  simp only [RoleArrayFrames.saved,RoleArrayFrames.saveOne,RoleArrayStackAt.pushed,
    RoleArrayFrames.slots,layout,Matrix.cons_val_zero,Matrix.cons_val_one]
  change setTape (setTape (Placement.replace headerPlacement v small) r.val (fun _ => blank) 0) stack
    (RoleArrayStack.parked ((Placement.replace headerPlacement v small).tape stack)
      ((Placement.replace headerPlacement v small).tape r.val)
      ((Placement.replace headerPlacement v small).head stack) n)
    ((Placement.replace headerPlacement v small).head stack+n)=
    Placement.replace headerPlacement (setTape (setTape v r.val (fun _ => blank) 0) stack
      (RoleArrayStack.parked (v.tape stack) (v.tape r.val) (v.head stack) n) (v.head stack+n)) small
  have hs := replace_setTape headerPlacement v small r.val (fun _ => blank) 0 (by
    intro j; rw [numeric_active]; exact hr j)
  have ht := replace_setTape headerPlacement (setTape v r.val (fun _ => blank) 0) small stack
    (RoleArrayStack.parked (v.tape stack) (v.tape r.val) (v.head stack) n) (v.head stack+n) (by
      intro j; rw [numeric_active]; exact stack_numeric j)
  have hf : (Placement.replace headerPlacement v small).head stack=v.head stack ∧
      (Placement.replace headerPlacement v small).tape stack=v.tape stack ∧
      (Placement.replace headerPlacement v small).tape r.val=v.tape r.val := by
    have hx (i : Fin (tapes s c)) (hi : ∀ j,i≠numeric j) :
        (Placement.replace headerPlacement v small).head i=v.head i ∧
        (Placement.replace headerPlacement v small).tape i=v.tape i := by
      obtain ⟨i,rfl⟩ := (headerPlacement (s:=s) (c:=c)).surjective i
      induction i using Fin.addCases with
      | left i => exact (hi i (numeric_active i)).elim
      | right i => simp only [Placement.replace,Placement.combine_head_extra,
          Placement.combine_tape_extra,Placement.extra]; trivial
    exact ⟨(hx stack stack_numeric).1,(hx stack stack_numeric).2,(hx r.val hr).2⟩
  rw [hf.1,hf.2.1,hf.2.2]
  rw [hs] at ht
  exact ht.symm


theorem master_replace (n : ℕ) (v : Tapes (tapes s c) 2) (small : Tapes 43 2) :
    RoleArrayFrames.saved layout [sourceRole] n (Placement.replace headerPlacement v small)=
      Placement.replace headerPlacement (RoleArrayFrames.saved layout [sourceRole] n v) small :=
  save_replace sourceRole source_numeric n v small

private theorem header_frame (v : Tapes (tapes s c) 2) (small : Tapes 43 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠numeric j) :
    (Placement.replace headerPlacement v small).head i=v.head i ∧
    (Placement.replace headerPlacement v small).tape i=v.tape i := by
  obtain ⟨i,rfl⟩ := (headerPlacement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i => exact (hi i (numeric_active i)).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra]; trivial

/-- All fixed parent-role saves commute with generated-header replacement. -/
theorem saved_replace (ops : List (RoleArrayFrames.Role (layout (s:=s) (c:=c))))
    (hr : ∀ r∈ops,∀ j,r.val≠numeric j) (n : ℕ) (v : Tapes (tapes s c) 2) (small : Tapes 43 2) :
    RoleArrayFrames.saved layout ops n (Placement.replace headerPlacement v small)=
      Placement.replace headerPlacement (RoleArrayFrames.saved layout ops n v) small := by
  induction ops generalizing v with
  | nil => rfl
  | cons r ops ih =>
    change RoleArrayFrames.saved layout ops n
      (RoleArrayFrames.saved layout [r] n (Placement.replace headerPlacement v small))=_
    rw [save_replace r (hr r List.mem_cons_self),ih (by intro r hr';exact hr r (List.mem_cons_of_mem _ hr'))]
    rfl

/-- Spectator entry commutes with numeric synthesis/cleanup on actual words. -/
theorem parked_replace (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2) (small : Tapes 43 2) :
    parked selected n (Placement.replace headerPlacement v small)=
      Placement.replace headerPlacement (parked selected n v) small := by
  have hr : ∀ r∈inactive (s:=s) selected,∀ j,r.val≠numeric j := by
    intro r hr j
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hr).1
    exact role_numeric k j
  unfold parked RoleArrayCall.entered
  rw [saved_replace _ hr]
  let w := RoleArrayFrames.saved layout (inactive selected) n v
  change RoleArrayMove.moved (RoleArrayCall.slots layout (role selected) sourceRole)
      (Placement.replace headerPlacement w small)=
    Placement.replace headerPlacement (RoleArrayMove.moved (RoleArrayCall.slots layout (role selected) sourceRole) w) small
  simp only [RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [(header_frame w small (roleTape selected) (role_numeric selected)).2]
  rw [replace_setTape _ _ _ source _ _ (by intro j; rw [numeric_active];exact source_numeric j),
    replace_setTape _ _ _ (roleTape selected) _ _ (by intro j; rw [numeric_active];exact role_numeric selected j)]

private theorem saved_headers (ops : List (RoleArrayFrames.Role (layout (s:=s) (c:=c))))
    (hr : ∀ r∈ops,∀ j,r.val≠numeric j) (n : ℕ) (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (RoleArrayFrames.saved layout ops n v)=Placement.active headerPlacement v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    rw [numeric_active]
    have hf := RoleArrayFrames.saved_frame layout ops n v (numeric i) (stack_numeric i).symm
      (by intro r hr';exact (hr r hr' i).symm)
    first | exact hf.1 | exact hf.2

private theorem parked_headers (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (parked selected n v)=Placement.active headerPlacement v := by
  have hr : ∀ r∈inactive (s:=s) selected,∀ j,r.val≠numeric j := by
    intro r hr j
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hr).1
    exact role_numeric k j
  have hh := saved_headers (inactive selected) hr n v
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have ha := congrArg (fun z => z.head i) hh
    have ht := congrArg (fun z => z.tape i) hh
    change (RoleArrayFrames.saved layout (inactive selected) n v).head (headerPlacement (Fin.castAdd _ i))=v.head (headerPlacement (Fin.castAdd _ i)) at ha
    change (RoleArrayFrames.saved layout (inactive selected) n v).tape (headerPlacement (Fin.castAdd _ i))=v.tape (headerPlacement (Fin.castAdd _ i)) at ht
    rw [numeric_active] at ha ht
    simp only [numeric_active,parked,RoleArrayCall.entered,
      RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,Matrix.cons_val_zero,Matrix.cons_val_one,setTape,
      Function.update_of_ne (source_numeric i).symm,Function.update_of_ne (role_numeric selected i).symm]
    first | exact ha | exact ht

private theorem replace_twice (v : Tapes (tapes s c) 2) (a b : Tapes 43 2) :
    Placement.replace headerPlacement (Placement.replace headerPlacement v a) b=
      Placement.replace headerPlacement v b := by simp only [Placement.replace,Placement.extra_combine]

/-- Erased header lifecycles leave precisely the actual source parking transform. -/
theorem masterOutput_eq (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    masterOutput sh rows ell metadataP rho left count slots right src dst v=
      RoleArrayFrames.saved layout [sourceRole] (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) v := by
  dsimp only [masterOutput]
  rw [master_replace,replace_twice,←hraw,←saved_headers [sourceRole] (by intro r hr j;simp only [List.mem_singleton] at hr;subst r;exact source_numeric j)]
  exact Placement.replace_active _ _

/-- The second erased lifecycle is exactly spectator save and selected move. -/
theorem vacantOutput_eq (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    vacantOutput selected sh rows ell metadataP rho left count slots right src dst v=
      parked selected (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) v := by
  dsimp only [vacantOutput]
  rw [parked_replace,replace_twice,←hraw,←parked_headers selected]
  exact Placement.replace_active _ _

private theorem clock_numeric (i : Fin 43) : clock (s:=s) (c:=c)≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := (CompactComplexNativeCodecFrame.headerSlot (s:=s) (c:=c) i).isLt
  simp only [clock,numeric,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem prepared_controls (merge : Bool) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank)) :
    RoleArrayFrames.Controls layout
      (RecursiveChildQuotientsConstant.bits (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP merge))
      (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
        (CompactNativeRoleHeaders.prepared c merge sh rows ell metadataP rho left count slots right src dst))) := by
  let p := CompactNativeRoleHeaders.prepared c merge sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)
  let N := CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP merge
  have hf := header_frame v (ActiveRepairRankHeadersCommands.bank p) clock clock_numeric
  have ha := Placement.active_replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)
  have hh := congrArg (fun z => z.head (27:Fin 43)) ha
  have ht := congrArg (fun z => z.tape (27:Fin 43)) ha
  change w.head (headerPlacement (Fin.castAdd _ 27))=(ActiveRepairRankHeadersCommands.bank p).head 27 at hh
  change w.tape (headerPlacement (Fin.castAdd _ 27))=(ActiveRepairRankHeadersCommands.bank p).tape 27 at ht
  rw [numeric_active] at hh ht
  refine ⟨hf.1.trans hclock.1,hf.2.trans hclock.2,hh,?_⟩
  change w.tape (numeric 27)=CountedLoopReuseAlphabet.binary (RecursiveChildQuotientsConstant.bits N)
  rw [ht,RoleArrayStackMoves.binary_descriptor,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  simp [p,N,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,
    CompactNativeRoleHeaders.prepared,CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,Tapes.append,Fin.addCases,Nat.mul_assoc]

private theorem role_injective : Function.Injective (role (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k => k.val.val) h
  simp only [role,roleTape,CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem role_source (j : Fin c) : role (s:=s) j≠sourceRole := by
  intro h
  have hv := congrArg (fun k => k.val.val) h
  simp only [role,roleTape,CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    sourceRole,source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem inactive_nodup (selected : Fin c) : (inactive (s:=s) selected).Nodup :=
  (List.nodup_ofFn_ofInjective role_injective).filter _
private theorem selected_not_inactive (selected : Fin c) : role (s:=s) selected∉inactive selected := by
  simp [inactive]
private theorem source_not_inactive (selected : Fin c) : sourceRole (s:=s)∉inactive selected := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp h).1
  exact role_source i hi

def vacantReturnProgram (selected : Fin c) := seq
  (seq (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c true))
    (RoleArrayCallBoundary.returnProgram (a:=2) (layout (s:=s) (c:=c))
      (inactive selected) (role selected) sourceRole (role_source selected)))
  (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)

/-- Genuine generated-count spectator recovery. The result word may be any
supported selected payload: instantiate `v` with that desired returned bank. -/
theorem vacant_return_runs (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ v.tape source=(fun _ => blank))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true))
    (hfree : RoleArrayFrames.Free layout (inactive selected)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) v) :
    HoareTime (vacantReturnProgram selected)
      (fun z => z=vacantOutput selected sh rows ell metadataP rho left count slots right src dst v)
      (fun z => z=v)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
        (92*(inactive (s:=s) selected).length+88)*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
          (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2) := by
  let p := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)
  let N := CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true
  let b := vacantOutput selected sh rows ell metadataP rho left count slots right src dst v
  have hb : b=parked selected N v := vacantOutput_eq selected sh rows ell metadataP rho left count slots right src dst v hraw
  have hbraw : Placement.active headerPlacement b=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) := by
    rw [hb,parked_headers,hraw]
  have hp := Placement.hoare_at (CompactNativeRoleHeaders.runs c true sh rows ell metadataP rho left count slots
    right src dst hc hr hgroup hG hA hK) headerPlacement b hbraw
  have hp' : HoareTime (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c true))
      (fun z => z=b) (fun z => z=parked selected N w)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :=
    hp.consequence (fun _ h => h) (by rintro z ⟨u,rfl,rfl⟩; rw [hb,←parked_replace]) le_rfl
  have hctrl := prepared_controls true sh rows ell metadataP rho left count slots right src dst v hclock
  have hpos : 0<N := by unfold N CompactComplexSpectatorVolumeHeaders.streamVolume CompactComplexSpectatorVolumeHeaders.roleRows; positivity
  have hwroles (j : Fin c) : w.head (roleTape j)=0 ∧ RoleArrayStack.Supported (w.tape (roleTape j)) N := by
    have hf := header_frame v (ActiveRepairRankHeadersCommands.bank p) (roleTape j) (role_numeric j)
    exact ⟨hf.1.trans (hroles j).1,by change RoleArrayStack.Supported ((Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)).tape (roleTape j)) N;rw [hf.2];exact (hroles j).2⟩
  have hs := header_frame v (ActiveRepairRankHeadersCommands.bank p) source source_numeric
  have hf := header_frame v (ActiveRepairRankHeadersCommands.bank p) stack stack_numeric
  have hwfree : RoleArrayFrames.Free layout (inactive selected) N w := by
    intro z hz hlt
    change w.tape stack z=blank
    change w.head stack≤z at hz
    change z<w.head stack+_ at hlt
    rw [hf.1] at hz hlt
    rw [hf.2]
    exact hfree z hz hlt
  have he := RoleArrayCallBoundary.return_hoare layout (inactive selected) (inactive_nodup selected)
    (role selected) sourceRole (role_source selected) (selected_not_inactive selected) (source_not_inactive selected)
    w (RecursiveChildQuotientsConstant.bits N) N (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) hpos hctrl
    (by intro r hr';obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hr').1;exact hwroles j)
    hwfree (hwroles selected) ⟨hs.1.trans hsource.1,hs.2.trans hsource.2⟩
  have hclean := Placement.hoare_at (CompactNativeRoleHeaders.cleanup_runs c true sh rows ell metadataP rho left
    count slots right src dst) headerPlacement w (Placement.active_replace _ _ _)
  have hclean' : HoareTime (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)
      (fun z => z=w) (fun z => z=v)
      (ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup p) :=
    hclean.consequence (fun _ h => h) (by rintro z ⟨u,rfl,rfl⟩; rw [replace_twice,←hraw,Placement.replace_active]) le_rfl
  exact ((hp'.seq he).seq hclean').consequence (fun _ h => h) (fun _ h => h)
    (by dsimp only [N,p];omega)

/-- The retained full parent source is restored after all inactive-role frames. -/
def masterReturnProgram := seq
  (seq (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c false))
    (RoleArrayFrames.popProgram (a:=2) (layout (s:=s) (c:=c)) [sourceRole]))
  (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)

theorem master_return_runs (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false))
    (hfree : RoleArrayFrames.Free layout [sourceRole]
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) v) :
    HoareTime (masterReturnProgram (s:=s) (c:=c))
      (fun z => z=masterOutput sh rows ell metadataP rho left count slots right src dst v)
      (fun z => z=v)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
        92*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
          (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2) := by
  let p := CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)
  let N := CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false
  let b := masterOutput sh rows ell metadataP rho left count slots right src dst v
  have hb : b=RoleArrayFrames.saved layout [sourceRole] N v :=
    masterOutput_eq sh rows ell metadataP rho left count slots right src dst v hraw
  have hbraw : Placement.active headerPlacement b=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) := by
    rw [hb,saved_headers [sourceRole] (by intro r hr' j;simp only [List.mem_singleton] at hr';subst r;exact source_numeric j),hraw]
  have hp := Placement.hoare_at (CompactNativeRoleHeaders.runs c false sh rows ell metadataP rho left count slots
    right src dst hc hr hgroup hG hA hK) headerPlacement b hbraw
  have hp' : HoareTime (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c false))
      (fun z => z=b) (fun z => z=RoleArrayFrames.saved layout [sourceRole] N w)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :=
    hp.consequence (fun _ h => h) (by rintro z ⟨u,rfl,rfl⟩; rw [hb,←master_replace]) le_rfl
  have hctrl := prepared_controls false sh rows ell metadataP rho left count slots right src dst v hclock
  have hpos : 0<N := by unfold N CompactComplexSpectatorVolumeHeaders.streamVolume CompactComplexSpectatorVolumeHeaders.roleRows; positivity
  have hs := header_frame v (ActiveRepairRankHeadersCommands.bank p) source source_numeric
  have hf := header_frame v (ActiveRepairRankHeadersCommands.bank p) stack stack_numeric
  have hwsource : w.head source=0 ∧ RoleArrayStack.Supported (w.tape source) N :=
    ⟨hs.1.trans hsource.1,by change RoleArrayStack.Supported ((Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p)).tape source) N;rw [hs.2];exact hsource.2⟩
  have hwfree : RoleArrayFrames.Free layout [sourceRole] N w := by
    intro z hz hlt
    change w.tape stack z=blank
    change w.head stack≤z at hz
    change z<w.head stack+_ at hlt
    rw [hf.1] at hz hlt
    rw [hf.2]
    exact hfree z hz hlt
  have he := RoleArrayFrames.pop_hoare_linear layout [sourceRole] (by simp) w
    (RecursiveChildQuotientsConstant.bits N) N (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) hpos hctrl
    (by intro r hr';simp only [List.mem_singleton] at hr';subst r;exact hwsource) hwfree
  have hclean := Placement.hoare_at (CompactNativeRoleHeaders.cleanup_runs c false sh rows ell metadataP rho left
    count slots right src dst) headerPlacement w (Placement.active_replace _ _ _)
  have hclean' : HoareTime (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)
      (fun z => z=w) (fun z => z=v)
      (ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup p) :=
    hclean.consequence (fun _ h => h) (by rintro z ⟨u,rfl,rfl⟩; rw [replace_twice,←hraw,Placement.replace_active]) le_rfl
  exact ((hp'.seq he).seq hclean').consequence (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_singleton];dsimp only [N,p];omega)

/-- Enough blank stack suffix for this node's full master-and-spectator frame. -/
def Free (selected : Fin c) (masterVolume roleVolume : ℕ) (v : Tapes (tapes s c) 2) : Prop :=
  ∀ z,v.head stack≤z →
    z<v.head stack+(masterVolume : ℕ)+((inactive (s:=s) selected).length*roleVolume : ℕ) → v.tape stack z=blank

/-- Reverse order is essential: inactive-role frames first, master source last. -/
def program (selected : Fin c) := seq (vacantReturnProgram (s:=s) selected) (masterReturnProgram (s:=s) (c:=c))

/-- Actual complete entry-frame recovery on the same fixed tape bank, including
all previous ancestor stack cells, their original head, and all raw headers. -/
theorem runs (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true))
    (hfree : Free selected (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) v) :
    HoareTime (program selected)
      (fun z => z=output selected sh rows ell metadataP rho left count slots right src dst v)
      (fun z => z=v)
      ((ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
          (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
          (92*(inactive (s:=s) selected).length+88)*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
            (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2)+
        (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
          (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
          92*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
            (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2)+1) := by
  let N0 := CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false
  let N1 := CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true
  let m := masterOutput sh rows ell metadataP rho left count slots right src dst v
  have hm : m=RoleArrayFrames.saved layout [sourceRole] N0 v :=
    masterOutput_eq sh rows ell metadataP rho left count slots right src dst v hraw
  have hmraw : Placement.active headerPlacement m=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) := by
    dsimp only [m,masterOutput]
    exact Placement.active_replace _ _ _
  have hmclock : m.head clock=0 ∧ m.tape clock=(fun _ => blank) := by
    rw [hm]
    have hf := RoleArrayFrames.saved_frame layout [sourceRole] N0 v clock layout.stack_clock.symm
      (by intro r hr';simp only [List.mem_singleton] at hr';subst r;exact sourceRole.property.2.1.symm)
    exact ⟨hf.1.trans hclock.1,hf.2.trans hclock.2⟩
  have hmroles (j : Fin c) : m.head (roleTape j)=0 ∧ RoleArrayStack.Supported (m.tape (roleTape j)) N1 := by
    rw [hm]
    have hf := RoleArrayFrames.saved_frame layout [sourceRole] N0 v (roleTape j) (role j).property.1
      (by intro r hr';simp only [List.mem_singleton] at hr';subst r;intro h;exact role_source j (Subtype.ext h))
    exact ⟨hf.1.trans (hroles j).1,by rw [hf.2];exact (hroles j).2⟩
  have hmhead : m.head stack=v.head stack+(N0 : ℕ) := by
    rw [hm]
    have hh := RoleArrayFrames.saved_head (layout (s:=s) (c:=c)) [sourceRole (s:=s) (c:=c)] N0 v
    simp only [List.length_cons,List.length_nil,Nat.zero_add,one_mul] at hh
    exact hh
  have hmfree : RoleArrayFrames.Free layout (inactive selected) N1 m := by
    intro z hz hlt
    change m.tape stack z=blank
    change m.head stack≤z at hz
    change z<m.head stack+_ at hlt
    rw [hmhead] at hz hlt
    rw [hm]
    have ho := RoleArrayFrames.saved_outside (layout (s:=s) (c:=c)) [sourceRole (s:=s) (c:=c)] N0 v z
      (by right;simp only [List.length_cons,List.length_nil,Nat.zero_add,one_mul];exact hz)
    change (RoleArrayFrames.saved layout [sourceRole] N0 v).tape stack z=v.tape stack z at ho
    rw [ho]
    exact hfree z (by omega) hlt
  have hv := vacant_return_runs (s:=s) selected sh rows ell metadataP rho left count slots right src dst m
    hc hr hgroup hG hA hK hmraw hmclock
    (master_source_blank sh rows ell metadataP rho left count slots right src dst v) hmroles hmfree
  have hmasterfree : RoleArrayFrames.Free layout [sourceRole] N0 v := by
    intro z hz hlt
    change v.tape stack z=blank
    change v.head stack≤z at hz
    change z<v.head stack+([sourceRole].length*N0 : ℕ) at hlt
    simp only [List.length_singleton,one_mul] at hlt
    exact hfree z hz (by omega)
  have hruns := master_return_runs (s:=s) (c:=c) sh rows ell metadataP rho left count slots right src dst v
    hc hr hgroup hG hA hK hraw hclock hsource hmasterfree
  change HoareTime (masterReturnProgram (s:=s) (c:=c)) (fun z => z=m) (fun z => z=v) _ at hruns
  have h := hv.seq hruns
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Parking an unrelated frame commutes with changing a retained role payload. -/
theorem saved_setTape {t a : ℕ} (L : RoleArrayFrames.Layout t)
    (ops : List (RoleArrayFrames.Role L)) (n : ℕ) (v : Tapes t a) (i : Fin t)
    (f : ℤ → Fin (a+4)) (p : ℤ) (hs : i≠L.stack) (hi : ∀ r∈ops,i≠r.val) :
    RoleArrayFrames.saved L ops n (setTape v i f p)=setTape (RoleArrayFrames.saved L ops n v) i f p := by
  induction ops generalizing v with
  | nil => rfl
  | cons r ops ih =>
    have hir := hi r List.mem_cons_self
    have h1 : RoleArrayFrames.saveOne L r n (setTape v i f p)=
        setTape (RoleArrayFrames.saveOne L r n v) i f p := by
      have hri : r.val≠i := hir.symm
      apply congrArg₂ Tapes.mk <;> funext j <;>
        by_cases hj : j=i <;> by_cases hr : j=r.val <;> by_cases hk : j=L.stack <;>
        simp_all [RoleArrayFrames.saveOne,RoleArrayStackAt.pushed,RoleArrayFrames.slots,setTape]
    change RoleArrayFrames.saved L ops n (RoleArrayFrames.saveOne L r n (setTape v i f p))=_
    rw [h1,ih _ (by intro r hr;exact hi r (List.mem_cons_of_mem _ hr))]
    rfl

private theorem selected_inactive_frame (selected : Fin c) :
    ∀ r∈inactive (s:=s) selected,roleTape selected≠r.val := by
  intro r hr he
  exact selected_not_inactive selected (by
    have h : role (s:=s) selected=r := Subtype.ext he
    exact h.symm ▸ hr)

/-- The selected replacement becomes the child source; no saved spectator or
ancestor stack cell depends on the selected numerator word. -/
theorem parked_set_selected (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) :
    parked selected n (setTape v (roleTape selected) f 0)=setTape (parked selected n v) source f 0 := by
  unfold parked RoleArrayCall.entered
  rw [saved_setTape layout (inactive selected) n v (roleTape selected) f 0
    (role selected).property.1 (selected_inactive_frame selected)]
  have hne : roleTape (s:=s) selected≠source := by intro h;exact role_source selected (Subtype.ext h)
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases hs : i=source <;> by_cases hr : i=roleTape selected <;>
    simp_all [RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,setTape]

private theorem selected_headers (selected : Fin c) (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) :
    Placement.active headerPlacement (setTape v (roleTape selected) f 0)=Placement.active headerPlacement v := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [numeric_active,setTape,Function.update_of_ne (role_numeric selected i).symm]

/-- Pure representation of both genuinely executed generated-count lifecycles. -/
theorem output_eq (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    output selected sh rows ell metadataP rho left count slots right src dst v=
      parked selected (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true)
        (RoleArrayFrames.saved layout [sourceRole]
          (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) v) := by
  unfold output
  rw [vacantOutput_eq selected sh rows ell metadataP rho left count slots right src dst _
    (by dsimp only [masterOutput];exact Placement.active_replace _ _ _),
    masterOutput_eq sh rows ell metadataP rho left count slots right src dst v hraw]

/-- Replacing only the selected parent result changes only the entered source.
All parked ancestors and spectators are literally the same physical frames. -/
theorem output_set_selected (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    output selected sh rows ell metadataP rho left count slots right src dst (setTape v (roleTape selected) f 0)=
      setTape (output selected sh rows ell metadataP rho left count slots right src dst v) source f 0 := by
  rw [output_eq selected sh rows ell metadataP rho left count slots right src dst _
      ((selected_headers selected v f).trans hraw),
    output_eq selected sh rows ell metadataP rho left count slots right src dst v hraw]
  rw [saved_setTape layout [sourceRole] _ v (roleTape selected) f 0 (role selected).property.1
    (by intro r hr;simp only [List.mem_singleton] at hr;subst r;intro h;exact role_source selected (Subtype.ext h)),
    parked_set_selected]

/-- Literal generated-count return cost, with every sequence join paid. -/
def cost (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) :=
  ((ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
          (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
          (92*(inactive (s:=s) selected).length+88)*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
            (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2)+
        (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
          (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
          92*CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
            (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2)+1)

/-- An arbitrary supported actual child result is recovered into the selected
parent role while retaining the old master source and every ancestor frame. -/
theorem runs_result (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) (v : Tapes (tapes s c) 2)
    (returned : ℤ → Fin 6)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true))
    (hfree : Free selected (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) v)
    (hreturned : RoleArrayStack.Supported returned (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true)) :
    HoareTime (program selected)
      (fun z => z=setTape (output selected sh rows ell metadataP rho left count slots right src dst v) source returned 0)
      (fun z => z=setTape v (roleTape selected) returned 0)
      (cost (s:=s) selected sh rows ell metadataP rho left count slots right src dst) := by
  let u := setTape v (roleTape selected) returned 0
  have hraw' : Placement.active headerPlacement u=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) :=
    (selected_headers selected v returned).trans hraw
  have hclock' : u.head clock=0 ∧ u.tape clock=(fun _ => blank) := by
    have hn : clock (s:=s) (c:=c)≠roleTape selected := (role selected).property.2.1.symm
    simpa only [u,setTape,Function.update_of_ne hn] using hclock
  have hsource' : u.head source=0 ∧ RoleArrayStack.Supported (u.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) := by
    have hs : source (s:=s) (c:=c)≠roleTape selected := by intro h;exact role_source selected (Subtype.ext h.symm)
    simpa only [u,setTape,Function.update_of_ne hs] using hsource
  have hroles' (j : Fin c) : u.head (roleTape j)=0 ∧ RoleArrayStack.Supported (u.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) := by
    by_cases hj : j=selected
    · subst j
      simpa only [u,setTape,Function.update_self] using (show 0=0 ∧ RoleArrayStack.Supported returned _ from ⟨rfl,hreturned⟩)
    · have hn : roleTape (s:=s) j≠roleTape selected := by intro h;exact hj (role_injective (Subtype.ext h))
      simpa only [u,setTape,Function.update_of_ne hn] using hroles j
  have hfree' : Free selected (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) u := by
    have hs : stack (s:=s) (c:=c)≠roleTape selected := (role selected).property.1.symm
    simpa only [Free,u,setTape,Function.update_of_ne hs] using hfree
  have h := runs (s:=s) selected sh rows ell metadataP rho left count slots right src dst u
    hc hr hgroup hG hA hK hraw' hclock' hsource' hroles' hfree'
  rw [output_set_selected selected sh rows ell metadataP rho left count slots right src dst v returned hraw] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleReturn
