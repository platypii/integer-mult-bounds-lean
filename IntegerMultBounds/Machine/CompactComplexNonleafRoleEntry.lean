import IntegerMultBounds.Machine.RoleArrayCallBoundary
import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeBudget
import IntegerMultBounds.Machine.CompactComplexNativeCodecFrame

/-! First physical payload boundary for an unstopped complex child. Original
raw geometry generates the full-volume count to park the retained master source,
then independently generates the role-volume count; all parent spectators are parked
on one fixed payload-stack tape, the selected role moves to native source65,
and every permanent role tape becomes blank at head zero. All generated numeric
headers are then erased. This is payload entry, not child network execution:
the next row quotient/split and inherited-denominator handoff remain separate. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleEntry
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactComplexSpectatorTargetBank (numericSlot roleSlot)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open RoleArrayFrames (Layout Role)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

abbrev tapes (s c : ℕ) := permanentTapes s c+2

def numeric (i : Fin 43) : Fin (tapes s c) :=
  Fin.castAdd 2 (CompactComplexNativeCodecFrame.headerSlot i)
def source : Fin (tapes s c) := Fin.castAdd 2 (numericSlot (s:=s) (c:=c) 65)
def roleTape (j : Fin c) : Fin (tapes s c) := Fin.castAdd 2 (roleSlot (s:=s) j)
def stack : Fin (tapes s c) := Fin.natAdd (permanentTapes s c) 0
def clock : Fin (tapes s c) := Fin.natAdd (permanentTapes s c) 1

private theorem numeric_injective : Function.Injective (numeric (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem role_numeric (j : Fin c) (i : Fin 43) : roleTape (s:=s) j≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [roleTape,roleSlot,CompactComplexNativeRoleBridge.roleSlot,numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    CompactComplexControllerNativeFrame.tapes,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_numeric (i : Fin 43) : source (s:=s) (c:=c)≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [source,numericSlot,numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem extra_numeric (i : Fin 2) (j : Fin 43) :
    Fin.natAdd (permanentTapes s c) i≠numeric j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := (CompactComplexNativeCodecFrame.headerSlot (s:=s) (c:=c) j).isLt
  simp only [numeric,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem numeric_size : 43+(tapes s c-43)=tapes s c := by
  unfold tapes permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes
  omega

def headerPlacement : Fin (43+(tapes s c-43)) ≃ Fin (tapes s c) :=
  InjectivePlacement.placement numeric numeric_injective numeric_size

def headerProgram (ops : List ButterflyAxisHeadersArithmetic.Op) :=
  Placement.placed (ButterflyAxisHeadersArithmetic.compile (a:=2) ops).2 (headerPlacement (s:=s) (c:=c))

private theorem active_header (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement v=⟨fun i => v.head (numeric i),fun i => v.tape (numeric i)⟩ :=
  InjectivePlacement.active_bank numeric numeric_injective numeric_size v

private theorem replace_frame (v : Tapes (tapes s c) 2) (small : Tapes 43 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠numeric j) :
    (Placement.replace headerPlacement v small).head i=v.head i ∧
      (Placement.replace headerPlacement v small).tape i=v.tape i := by
  obtain ⟨i,rfl⟩ := (headerPlacement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i =>
    have he := InjectivePlacement.active_slot (numeric (s:=s) (c:=c)) numeric_injective numeric_size i
    exact (hi i he).elim
  | right i =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

def layout : Layout (tapes s c) where
  stack := stack
  clock := clock
  count := numeric 27
  stack_clock := by intro h; have hv := congrArg Fin.val h; simp [stack,clock] at hv
  stack_count := extra_numeric 0 27
  clock_count := extra_numeric 1 27

private theorem role_extra (j : Fin c) (i : Fin 2) :
    roleTape (s:=s) j≠Fin.natAdd (permanentTapes s c) i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := (roleSlot (s:=s) j).isLt
  simp only [roleTape,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_extra (i : Fin 2) :
    source (s:=s) (c:=c)≠Fin.natAdd (permanentTapes s c) i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := (numericSlot (s:=s) (c:=c) 65).isLt
  simp only [source,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def role (j : Fin c) : Role (layout (s:=s) (c:=c)) :=
  ⟨roleTape j,role_extra j 0,role_extra j 1,role_numeric j 27⟩
def sourceRole : Role (layout (s:=s) (c:=c)) :=
  ⟨source,source_extra 0,source_extra 1,source_numeric 27⟩

private theorem role_injective : Function.Injective (role (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k => k.val.val) h
  simp only [role,roleTape,roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem role_source (j : Fin c) : role (s:=s) j≠sourceRole := by
  intro h
  have hv := congrArg (fun k => k.val.val) h
  simp only [role,roleTape,roleSlot,CompactComplexNativeRoleBridge.roleSlot,sourceRole,source,numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def inactive (selected : Fin c) : List (Role (layout (s:=s) (c:=c))) :=
  (List.ofFn (role (s:=s))).filter (fun i => i≠role selected)

private theorem inactive_nodup (selected : Fin c) : (inactive (s:=s) selected).Nodup :=
  (List.nodup_ofFn_ofInjective role_injective).filter _

private theorem selected_not_inactive (selected : Fin c) : role (s:=s) selected∉inactive selected := by
  simp [inactive]

private theorem source_not_inactive (selected : Fin c) : sourceRole (s:=s)∉inactive selected := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp h).1
  exact role_source i hi

private theorem inactive_mem (selected j : Fin c) (hj : j≠selected) : role (s:=s) j∈inactive selected := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨j,rfl⟩,by simpa only [ne_eq,role_injective.eq_iff,decide_eq_true_eq] using hj⟩

def parked (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2) :=
  RoleArrayCall.entered layout (inactive selected) (role selected) sourceRole n v

def entryProgram (selected : Fin c) :=
  RoleArrayCallBoundary.entryProgram (a:=2) (layout (s:=s) (c:=c)) (inactive selected) (role selected) sourceRole (role_source selected)

def vacantProgram (selected : Fin c) := seq
  (seq (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c true)) (entryProgram (s:=s) selected))
  (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)

/-- Exact payload entry endpoint, with every generated numeric word erased. -/
def vacantOutput (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :=
  let raw := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let prepared := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  Placement.replace headerPlacement
    (parked selected (streamVolume sh c rows ell metadataP true)
      (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)))
    (ActiveRepairRankHeadersCommands.bank raw)

private theorem parked_header (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (parked selected n v)=Placement.active headerPlacement v := by
  rw [active_header,active_header]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hf := RoleArrayFrames.saved_frame layout (inactive selected) n v (numeric i)
      (extra_numeric 0 i).symm (fun j hj => by
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hj).1
        exact (role_numeric j i).symm)
    simp only [parked,RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,
      Matrix.cons_val_zero,Matrix.cons_val_one,setTape,Function.update_of_ne (source_numeric i).symm,
      Function.update_of_ne (role_numeric selected i).symm]
    first | exact hf.1 | exact hf.2

/-- Raw retained descriptors synthesize the count used by physical parking;
no initialized length, child bank or recursive callback is supplied. -/
theorem vacant_source_runs (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ v.tape source=(fun _ => blank))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (streamVolume sh c rows ell metadataP true)) :
    HoareTime (vacantProgram selected)
      (fun z => z=v)
      (fun z => z=vacantOutput selected sh rows ell metadataP rho left count slots right src dst v)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
        (88*(inactive (s:=s) selected).length+88)*streamVolume sh c rows ell metadataP true+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
          (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2) := by
  let prepared := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let v1 := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)
  let N := streamVolume sh c rows ell metadataP true
  have hp := Placement.hoare_at (CompactNativeRoleHeaders.runs c true sh rows ell metadataP rho left count slots
    right src dst hc hr hgroup hG hA hK) headerPlacement v hraw
  have hp' : HoareTime (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c true))
      (fun z => z=v) (fun z => z=v1)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) := by
    exact hp.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl
  have hctrl : RoleArrayFrames.Controls layout (bits N) v1 := by
    have hf := replace_frame v (ActiveRepairRankHeadersCommands.bank prepared) clock (extra_numeric 1)
    have hactive := Placement.active_replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)
    rw [active_header] at hactive
    have hh := congrArg (fun z => z.head (27:Fin 43)) hactive
    have ht := congrArg (fun z => z.tape (27:Fin 43)) hactive
    refine ⟨hf.1.trans hclock.1,hf.2.trans hclock.2,?_,?_⟩
    · exact hh
    · change v1.tape (numeric 27)=CountedLoopReuseAlphabet.binary (bits N)
      change v1.tape (numeric 27)=(ActiveRepairRankHeadersCommands.bank prepared).tape 27 at ht
      rw [ht,RoleArrayStackMoves.binary_descriptor,BinaryDescriptorStackRoundtrip.descriptor_encoded]
      simp [prepared,N,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
        ActiveRepairRankHeadersCommands.caller,CompactNativeRoleHeaders.prepared,
        streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Tapes.append,Fin.addCases,Nat.mul_assoc]
  have hpos : 0<N := by unfold N streamVolume CompactComplexSpectatorVolumeHeaders.roleRows; simp only [ite_true]; positivity
  have hrole (j : Fin c) : v1.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v1.tape (roleTape j)) N := by
    have hf := replace_frame v (ActiveRepairRankHeadersCommands.bank prepared) (roleTape j) (role_numeric j)
    exact ⟨hf.1.trans (hroles j).1,by rw [hf.2];exact (hroles j).2⟩
  have hs := replace_frame v (ActiveRepairRankHeadersCommands.bank prepared) source source_numeric
  have he := RoleArrayCallBoundary.entry_hoare layout (inactive selected) (inactive_nodup selected)
    (role selected) sourceRole (role_source selected) (selected_not_inactive selected) (source_not_inactive selected)
    v1 (bits N) N (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _) hpos hctrl
    (by intro i hi;obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hi).1;exact hrole j)
    (hrole selected) ⟨hs.1.trans hsource.1,hs.2.trans hsource.2⟩
  have ha : Placement.active headerPlacement (parked selected N v1)=ActiveRepairRankHeadersCommands.bank prepared := by
    rw [parked_header,Placement.active_replace]
  have hclean := Placement.hoare_at (CompactNativeRoleHeaders.cleanup_runs c true sh rows ell metadataP rho left
    count slots right src dst) headerPlacement (parked selected N v1) ha
  have hclean' : HoareTime (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)
      (fun z => z=parked selected N v1)
      (fun z => z=vacantOutput selected sh rows ell metadataP rho left count slots right src dst v)
      (ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared) :=
    hclean.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩;rfl) le_rfl
  exact ((hp'.seq he).seq hclean').consequence (fun _ h => h) (fun _ h => h) (by dsimp only [N,prepared]; omega)

/-- First vacate the retained master source, above all existing ancestor data. -/
def masterProgram := seq
  (seq (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c false))
    (RoleArrayFrames.pushProgram (a:=2) (layout (s:=s) (c:=c)) [sourceRole]))
  (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)

def masterOutput (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :=
  let raw := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let prepared := CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst
  Placement.replace headerPlacement
    (RoleArrayFrames.saved layout [sourceRole] (streamVolume sh c rows ell metadataP false)
      (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)))
    (ActiveRepairRankHeadersCommands.bank raw)

private theorem master_header (n : ℕ) (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (RoleArrayFrames.saved layout [sourceRole] n v)=
      Placement.active headerPlacement v := by
  rw [active_header,active_header]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have hf := RoleArrayFrames.saved_frame layout [sourceRole] n v (numeric i)
      (extra_numeric 0 i).symm (by
        intro j hj
        simp only [List.mem_singleton] at hj
        subst j
        exact (source_numeric i).symm)
    first | exact hf.1 | exact hf.2

/-- The real full-volume source is parked, without assuming it initially blank. -/
theorem master_runs (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (streamVolume sh c rows ell metadataP false)) :
    HoareTime (masterProgram (s:=s) (c:=c)) (fun z => z=v)
      (fun z => z=masterOutput sh rows ell metadataP rho left count slots right src dst v)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
        88*streamVolume sh c rows ell metadataP false+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
          (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2) := by
  let prepared := CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst
  let v1 := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)
  let N := streamVolume sh c rows ell metadataP false
  have hp := Placement.hoare_at (CompactNativeRoleHeaders.runs c false sh rows ell metadataP rho left count slots
    right src dst hc hr hgroup hG hA hK) headerPlacement v hraw
  have hp' : HoareTime (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule c false))
      (fun z => z=v) (fun z => z=v1)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) := by
    exact hp.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl
  have hctrl : RoleArrayFrames.Controls layout (bits N) v1 := by
    have hf := replace_frame v (ActiveRepairRankHeadersCommands.bank prepared) clock (extra_numeric 1)
    have hactive := Placement.active_replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)
    rw [active_header] at hactive
    have hh := congrArg (fun z => z.head (27:Fin 43)) hactive
    have ht := congrArg (fun z => z.tape (27:Fin 43)) hactive
    refine ⟨hf.1.trans hclock.1,hf.2.trans hclock.2,?_,?_⟩
    · exact hh
    · change v1.tape (numeric 27)=CountedLoopReuseAlphabet.binary (bits N)
      change v1.tape (numeric 27)=(ActiveRepairRankHeadersCommands.bank prepared).tape 27 at ht
      rw [ht,RoleArrayStackMoves.binary_descriptor,BinaryDescriptorStackRoundtrip.descriptor_encoded]
      simp [prepared,N,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
        ActiveRepairRankHeadersCommands.caller,CompactNativeRoleHeaders.prepared,
        streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Tapes.append,Fin.addCases,Nat.mul_assoc]
  have hpos : 0<N := by unfold N streamVolume CompactComplexSpectatorVolumeHeaders.roleRows; positivity
  have hs := replace_frame v (ActiveRepairRankHeadersCommands.bank prepared) source source_numeric
  have he := RoleArrayFrames.push_hoare_linear layout [sourceRole] (by simp)
    v1 (bits N) N (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _)
    hpos hctrl (by
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact ⟨hs.1.trans hsource.1,by change RoleArrayStack.Supported ((Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank prepared)).tape source) N; rw [hs.2]; exact hsource.2⟩)
  have ha : Placement.active headerPlacement (RoleArrayFrames.saved layout [sourceRole] N v1)=
      ActiveRepairRankHeadersCommands.bank prepared := by rw [master_header,Placement.active_replace]
  have hclean := Placement.hoare_at (CompactNativeRoleHeaders.cleanup_runs c false sh rows ell metadataP rho left
    count slots right src dst) headerPlacement (RoleArrayFrames.saved layout [sourceRole] N v1) ha
  have hclean' : HoareTime (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup)
      (fun z => z=RoleArrayFrames.saved layout [sourceRole] N v1)
      (fun z => z=masterOutput sh rows ell metadataP rho left count slots right src dst v)
      (ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared) :=
    hclean.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩;rfl) le_rfl
  exact ((hp'.seq he).seq hclean').consequence (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_singleton]; dsimp only [N,prepared]; omega)

/-- Header lifecycles and master parking preserve every other permanent slot. -/
theorem master_frame (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c))
    (hi : ∀ j,i≠numeric j) (hstack : i≠stack) (hsource : i≠source) :
    (masterOutput sh rows ell metadataP rho left count slots right src dst v).head i=v.head i ∧
    (masterOutput sh rows ell metadataP rho left count slots right src dst v).tape i=v.tape i := by
  unfold masterOutput
  have h1 := replace_frame v (ActiveRepairRankHeadersCommands.bank
    (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)) i hi
  have h2 := RoleArrayFrames.saved_frame layout [sourceRole] (streamVolume sh c rows ell metadataP false)
    (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
      (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)))
    i hstack (by intro j hj; simp only [List.mem_singleton] at hj; subst j; exact hsource)
  have h3 := replace_frame
    (RoleArrayFrames.saved layout [sourceRole] (streamVolume sh c rows ell metadataP false)
      (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
        (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst))))
    (ActiveRepairRankHeadersCommands.bank
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) i hi
  exact ⟨h3.1.trans (h2.1.trans h1.1),h3.2.trans (h2.2.trans h1.2)⟩

theorem master_source_blank (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :
    (masterOutput sh rows ell metadataP rho left count slots right src dst v).head source=0 ∧
    (masterOutput sh rows ell metadataP rho left count slots right src dst v).tape source=(fun _ => blank) := by
  unfold masterOutput
  have h := RoleArrayFrames.saved_role layout [sourceRole] (by simp)
    (streamVolume sh c rows ell metadataP false)
    (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
      (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)))
    sourceRole (by simp)
  have hf := replace_frame
    (RoleArrayFrames.saved layout [sourceRole] (streamVolume sh c rows ell metadataP false)
      (Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
        (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst))))
    (ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) source source_numeric
  exact ⟨hf.1.trans h.1,hf.2.trans h.2⟩

def program (selected : Fin c) := seq (masterProgram (s:=s) (c:=c)) (vacantProgram (s:=s) selected)

def output (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :=
  vacantOutput selected sh rows ell metadataP rho left count slots right src dst
    (masterOutput sh rows ell metadataP rho left count slots right src dst v)

/-- Actual two-stage entry starts from retained, possibly nonblank master source.
Both independent counts are physically generated and erased. -/
theorem runs (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (streamVolume sh c rows ell metadataP true)) :
    HoareTime (program selected) (fun z => z=v)
      (fun z => z=output selected sh rows ell metadataP rho left count slots right src dst v)
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c false)
        (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
        88*streamVolume sh c rows ell metadataP false+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
          (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2+
        (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c true)
          (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
          (88*(inactive (s:=s) selected).length+88)*streamVolume sh c rows ell metadataP true+
          ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
            (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2)+1) := by
  have hm := master_runs (s:=s) (c:=c) sh rows ell metadataP rho left count slots right src dst v hc hr hgroup hG hA hK
    hraw hclock hsource
  let m := masterOutput sh rows ell metadataP rho left count slots right src dst v
  have ha : Placement.active headerPlacement m=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) :=
    by
    dsimp only [m, masterOutput]
    exact Placement.active_replace (headerPlacement (s:=s) (c:=c)) _ _
  have hf := master_frame sh rows ell metadataP rho left count slots right src dst v (clock (s:=s) (c:=c)) (extra_numeric (s:=s) (c:=c) 1)
    (by intro h; have hv := congrArg Fin.val h; simp [clock,stack] at hv) (source_extra 1).symm
  have hrs (j : Fin c) : m.head (roleTape j)=0 ∧ RoleArrayStack.Supported (m.tape (roleTape j))
      (streamVolume sh c rows ell metadataP true) := by
    have hf := master_frame sh rows ell metadataP rho left count slots right src dst v (roleTape (s:=s) j)
      (role_numeric j) (role_extra j 0) (by intro h; exact role_source j (Subtype.ext h))
    exact ⟨hf.1.trans (hroles j).1,by rw [hf.2]; exact (hroles j).2⟩
  have hv := vacant_source_runs (s:=s) selected sh rows ell metadataP rho left count slots right src dst m
    hc hr hgroup hG hA hK ha ⟨hf.1.trans hclock.1,hf.2.trans hclock.2⟩
    (master_source_blank sh rows ell metadataP rho left count slots right src dst v) hrs
  change HoareTime (masterProgram (s:=s) (c:=c)) (fun z => z=v) (fun z => z=m) _ at hm
  have hh := hm.seq hv
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

private theorem parked_frame (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2)
    (i : Fin (tapes s c)) (hs : i≠stack) (hsource : i≠source)
    (hr : ∀ j,i≠roleTape j) :
    (parked selected n v).head i=v.head i ∧ (parked selected n v).tape i=v.tape i := by
  have hf := RoleArrayFrames.saved_frame layout (inactive selected) n v i hs (by
    intro j hj
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hj).1
    exact hr j)
  simpa only [parked,RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,
    Matrix.cons_val_zero,Matrix.cons_val_one,setTape,Function.update_of_ne hsource,
    Function.update_of_ne (hr selected)] using hf

/-- Every permanent controller or scalar slot outside source/role payloads is
framed. In particular numeric4/live7/target8/stack9/scalar43 are retained. -/
theorem output_frame (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c))
    (hi : ∀ j,i≠numeric j) (hstack : i≠stack) (hsource : i≠source) (hr : ∀ j,i≠roleTape j) :
    (output selected sh rows ell metadataP rho left count slots right src dst v).head i=v.head i ∧
    (output selected sh rows ell metadataP rho left count slots right src dst v).tape i=v.tape i := by
  let m := masterOutput sh rows ell metadataP rho left count slots right src dst v
  let p := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement m (ActiveRepairRankHeadersCommands.bank p)
  let b := parked selected (streamVolume sh c rows ell metadataP true) w
  have hm := master_frame sh rows ell metadataP rho left count slots right src dst v i hi hstack hsource
  have h1 := replace_frame m (ActiveRepairRankHeadersCommands.bank p) i hi
  have h2 := parked_frame selected (streamVolume sh c rows ell metadataP true) w i hstack hsource hr
  have h3 := replace_frame b (ActiveRepairRankHeadersCommands.bank
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) i hi
  exact ⟨h3.1.trans (h2.1.trans (h1.1.trans hm.1)),h3.2.trans (h2.2.trans (h1.2.trans hm.2))⟩

/-- All generated numeric words are erased back to the literal original bank. -/
theorem output_headers (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (output selected sh rows ell metadataP rho left count slots right src dst v)=
      ActiveRepairRankHeadersCommands.bank (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst) :=
  Placement.active_replace _ _ _

/-- The physical child source is exactly the selected parent payload; no child
bank or supplied result replaces this word. -/
theorem output_source (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :
    (output selected sh rows ell metadataP rho left count slots right src dst v).head source=0 ∧
    (output selected sh rows ell metadataP rho left count slots right src dst v).tape source=v.tape (roleTape selected) := by
  let m := masterOutput sh rows ell metadataP rho left count slots right src dst v
  let p := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement m (ActiveRepairRankHeadersCommands.bank p)
  let b := parked selected (streamVolume sh c rows ell metadataP true) w
  have he := RoleArrayCallBoundary.entered_payload layout (inactive selected) (role selected) sourceRole
    (role_source selected) (selected_not_inactive selected) (streamVolume sh c rows ell metadataP true) w
  have h3 := replace_frame b (ActiveRepairRankHeadersCommands.bank
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) source source_numeric
  have h1 := replace_frame m (ActiveRepairRankHeadersCommands.bank p) (roleTape selected) (role_numeric selected)
  have hm := master_frame sh rows ell metadataP rho left count slots right src dst v (roleTape selected)
    (role_numeric selected) (role_extra selected 0) (by intro h; exact role_source selected (Subtype.ext h))
  exact ⟨h3.1.trans he.2.2.1,h3.2.trans (he.2.2.2.trans (h1.2.trans hm.2))⟩

/-- Every role is physically vacant, ready for a fresh child role split. -/
theorem output_roles_blank (selected j : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :
    (output selected sh rows ell metadataP rho left count slots right src dst v).head (roleTape j)=0 ∧
    (output selected sh rows ell metadataP rho left count slots right src dst v).tape (roleTape j)=(fun _ => blank) := by
  let m := masterOutput sh rows ell metadataP rho left count slots right src dst v
  let p := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let w := Placement.replace headerPlacement m (ActiveRepairRankHeadersCommands.bank p)
  let N := streamVolume sh c rows ell metadataP true
  let b := parked selected N w
  have h3 := replace_frame b (ActiveRepairRankHeadersCommands.bank
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) (roleTape j) (role_numeric j)
  have hb : b.head (roleTape j)=0 ∧ b.tape (roleTape j)=(fun _ => blank) := by
    by_cases hj : j=selected
    · subst j
      have he := RoleArrayCallBoundary.entered_payload layout (inactive selected) (role selected) sourceRole
        (role_source selected) (selected_not_inactive selected) N w
      exact ⟨he.1,he.2.1⟩
    · have he := RoleArrayFrames.saved_role layout (inactive selected) (inactive_nodup selected) N w (role j)
        (inactive_mem selected j hj)
      have hjs : roleTape (s:=s) j≠roleTape selected := by
        intro h
        exact hj (role_injective (Subtype.ext h))
      simpa only [b,parked,RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,
        Matrix.cons_val_zero,Matrix.cons_val_one,setTape,
        Function.update_of_ne (show roleTape (s:=s) j≠source by intro h; exact role_source j (Subtype.ext h)),
        Function.update_of_ne hjs] using he
  exact ⟨h3.1.trans hb.1,h3.2.trans hb.2⟩

private theorem parked_stack (selected : Fin c) (n : ℕ) (v : Tapes (tapes s c) 2) :
    (parked selected n v).head stack=v.head stack+((inactive (s:=s) selected).length*n : ℕ) ∧
    (parked selected n v).tape stack=(RoleArrayFrames.saved layout (inactive selected) n v).tape stack := by
  have hh := RoleArrayFrames.saved_head layout (inactive selected) n v
  have hs : stack (s:=s) (c:=c)≠source := (source_extra 0).symm
  have hr : stack (s:=s) (c:=c)≠roleTape selected := (role_extra selected 0).symm
  simp only [parked,RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,role,sourceRole,
    Matrix.cons_val_zero,Matrix.cons_val_one,setTape,Function.update_of_ne hs,Function.update_of_ne hr]
  exact ⟨hh,trivial⟩

/-- The same fixed stack appends master data followed by inactive role data;
its prior ancestor prefix is not consumed or repositioned. -/
theorem output_stack_head (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) :
    (output selected sh rows ell metadataP rho left count slots right src dst v).head stack=
      v.head stack+(streamVolume sh c rows ell metadataP false : ℕ)+
        ((inactive (s:=s) selected).length*streamVolume sh c rows ell metadataP true : ℕ) := by
  let p0 := CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst
  let p1 := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let raw := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let w0 := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p0)
  let b0 := RoleArrayFrames.saved layout [sourceRole] (streamVolume sh c rows ell metadataP false) w0
  let m := Placement.replace headerPlacement b0 (ActiveRepairRankHeadersCommands.bank raw)
  let w1 := Placement.replace headerPlacement m (ActiveRepairRankHeadersCommands.bank p1)
  let b1 := parked selected (streamVolume sh c rows ell metadataP true) w1
  have hf0 := replace_frame v (ActiveRepairRankHeadersCommands.bank p0) stack (extra_numeric 0)
  have hh0 := RoleArrayFrames.saved_head layout [sourceRole] (streamVolume sh c rows ell metadataP false) w0
  have hf1 := replace_frame b0 (ActiveRepairRankHeadersCommands.bank raw) stack (extra_numeric 0)
  have hf2 := replace_frame m (ActiveRepairRankHeadersCommands.bank p1) stack (extra_numeric 0)
  have hh1 := (parked_stack selected (streamVolume sh c rows ell metadataP true) w1).1
  have hf3 := replace_frame b1 (ActiveRepairRankHeadersCommands.bank raw) stack (extra_numeric 0)
  simp only [List.length_singleton,one_mul] at hh0
  change b0.head stack=w0.head stack+(streamVolume sh c rows ell metadataP false : ℕ) at hh0
  have hh3 : (output selected sh rows ell metadataP rho left count slots right src dst v).head stack=b1.head stack := hf3.1
  rw [hh3,hh1,hf2.1,hf1.1,hh0,hf0.1]

/-- Every older ancestor cell and every cell above this new frame is exactly
preserved, even when the shared stack originally has a nonzero head. -/
theorem output_stack_outside (selected : Fin c) (sh : Shape) (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) (z : ℤ)
    (hz : z<v.head stack ∨
      v.head stack+(streamVolume sh c rows ell metadataP false : ℕ)+
        ((inactive (s:=s) selected).length*streamVolume sh c rows ell metadataP true : ℕ)≤z) :
    (output selected sh rows ell metadataP rho left count slots right src dst v).tape stack z=v.tape stack z := by
  let p0 := CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst
  let p1 := CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst
  let raw := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let w0 := Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank p0)
  let b0 := RoleArrayFrames.saved layout [sourceRole] (streamVolume sh c rows ell metadataP false) w0
  let m := Placement.replace headerPlacement b0 (ActiveRepairRankHeadersCommands.bank raw)
  let w1 := Placement.replace headerPlacement m (ActiveRepairRankHeadersCommands.bank p1)
  let b1 := parked selected (streamVolume sh c rows ell metadataP true) w1
  have hf0 := replace_frame v (ActiveRepairRankHeadersCommands.bank p0) stack (extra_numeric 0)
  have hh0 := RoleArrayFrames.saved_head layout [sourceRole] (streamVolume sh c rows ell metadataP false) w0
  have hf1 := replace_frame b0 (ActiveRepairRankHeadersCommands.bank raw) stack (extra_numeric 0)
  have hf2 := replace_frame m (ActiveRepairRankHeadersCommands.bank p1) stack (extra_numeric 0)
  have hf3 := replace_frame b1 (ActiveRepairRankHeadersCommands.bank raw) stack (extra_numeric 0)
  simp only [List.length_singleton,one_mul] at hh0
  change b0.head stack=w0.head stack+(streamVolume sh c rows ell metadataP false : ℕ) at hh0
  have h1 : w1.head stack=v.head stack+(streamVolume sh c rows ell metadataP false : ℕ) := by
    rw [hf2.1,hf1.1,hh0,hf0.1]
  have ho1 := RoleArrayFrames.saved_outside layout (inactive selected) (streamVolume sh c rows ell metadataP true)
    w1 z (by change z<w1.head stack ∨ w1.head stack+_≤z; rw [h1]; omega)
  have ho0 := RoleArrayFrames.saved_outside layout [sourceRole] (streamVolume sh c rows ell metadataP false)
    w0 z (by change z<w0.head stack ∨ w0.head stack+_≤z; rw [hf0.1]; simp only [List.length_singleton,one_mul]; omega)
  have ht3 : (output selected sh rows ell metadataP rho left count slots right src dst v).tape stack=b1.tape stack := hf3.2
  change (RoleArrayFrames.saved layout (inactive selected) (streamVolume sh c rows ell metadataP true) w1).tape stack z=w1.tape stack z at ho1
  change b0.tape stack z=w0.tape stack z at ho0
  rw [ht3,(parked_stack selected (streamVolume sh c rows ell metadataP true) w1).2,ho1,hf2.2,hf1.2,ho0,hf0.2]

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleEntry
