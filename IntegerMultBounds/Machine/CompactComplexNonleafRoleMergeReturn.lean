import IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge
import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrame
import IntegerMultBounds.Machine.CompactReservationNativePaddingBudget

/-! Actual nonleaf child-role merge and parent payload return on one unchanged
fixed bank. Returned source support follows from literal coefficient widths;
advanced live-denominator words are retained while parent and ancestor payload
frames are restored. No recursive run or numerical child semantics is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturn
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNonleafRoleEntry
open SharedPlacementAlphabet (setTape)
open CompactSpectatorLeafSetup (raw)
variable {s c : ℕ}

/-- An arbitrary completed native child array occupies exactly the parent
role volume. Support is derived from its actual serialized record widths. -/
theorem returned_supported (sh : Shape) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    RoleArrayStack.Supported (NativeZeroPadding.word (NativeZeroPaddingArray.word f))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true) := by
  apply RoleArrayStack.supported_word
  have h := CompactReservationNativePaddingBudget.word_length (CompactNativeRoleHeaders.recordWidth sh p) f hw
  rw [h]
  simp only [CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,ite_true]
  unfold ButterflySpectatorGeometry.Size
  simp only [Nat.mul_assoc]
  exact le_rfl

private theorem append_setTape {t u a : ℕ} (v : Tapes t a) (work : Tapes u a)
    (i : Fin t) (f : ℤ → Fin (a+4)) (p : ℤ) :
    (setTape v i f p).append work=setTape (v.append work) (Fin.castAdd u i) f p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    induction j using Fin.addCases with
    | left j =>
      by_cases hj : j=i
      · subst j; simp [setTape,Tapes.append]
      · have hn : Fin.castAdd u j≠Fin.castAdd u i := by intro h;exact hj (Fin.castAdd_injective _ _ h)
        simp [setTape,Tapes.append,hj,hn]
    | right j =>
      have hn : Fin.natAdd t j≠Fin.castAdd u i := by
        intro h;have hv := congrArg Fin.val h;have hi := i.isLt;simp only [Fin.val_natAdd,Fin.val_castAdd] at hv;omega
      simp [setTape,Tapes.append,hn]

private theorem extra_setTape_active {t n u a : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t a) (i : Fin n) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.extra e (setTape v (e (Fin.castAdd u i)) f p)=Placement.extra e v := by
  have hn (j : Fin u) : e (Fin.natAdd n j)≠e (Fin.castAdd u i) := by
    intro h
    have hv := congrArg Fin.val (e.injective h)
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  apply congrArg₂ Tapes.mk <;> funext j <;>
    simp only [setTape,Function.update_of_ne (hn j)]

private def sourceIndex : Fin (43+CompactNativeRoleInstall.rawCount c) := ⟨43,by
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount
  omega⟩

private theorem source_active :
    CompactComplexNonleafRoleSplit.placement (s:=s) (c:=c)
      (Fin.castAdd _ (sourceIndex (c:=c)))=Fin.castAdd 7 (source (s:=s) (c:=c)) := by
  unfold CompactComplexNonleafRoleSplit.placement
  rw [InjectivePlacement.active_slot]
  apply Fin.ext
  simp [sourceIndex,CompactComplexNonleafRoleSplit.slot,source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot]


private theorem numeric_active (j : Fin 43) :
    headerPlacement (s:=s) (c:=c) (Fin.castAdd (tapes s c-43) j)=numeric j := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

private theorem active_set_frame (v : Tapes (tapes s c) 2) (i : Fin (tapes s c))
    (hi : ∀ j,i≠numeric j) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.active headerPlacement (setTape v i f p)=Placement.active headerPlacement v := by
  apply congrArg₂ Tapes.mk <;> funext j <;>
    simp only [numeric_active,setTape,Function.update_of_ne (hi j).symm]

private theorem source_numeric (j : Fin 43) : source (s:=s) (c:=c)≠numeric j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [source,numeric,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_role (j : Fin c) : source (s:=s) (c:=c)≠roleTape j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [source,roleTape,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Once genuine child roles have merged and parent raw geometry is restored,
the exact whole-bank endpoint is the existing framed return input. -/
theorem parent_replacement (selected : Fin c) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ)
    (hi : ∀ j,i≠numeric j) (hr : ∀ j,i≠roleTape j) :
    Placement.replace CompactComplexNonleafRoleSplit.placement
      ((setTape (output selected sh rows ell p rho left count slots right src dst v) i advanced head).append
        (SharedBank.empty 7 2))
      (CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))=
    (setTape (setTape (output selected sh rows ell p rho left count slots right src dst v) i advanced head)
      source (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) 0).append (SharedBank.empty 7 2) := by
  let b := setTape (output selected sh rows ell p rho left count slots right src dst v) i advanced head
  let word := NativeZeroPadding.word (NativeZeroPaddingArray.word f)
  let target := setTape b source word 0
  have hbraw : Placement.active headerPlacement b=ActiveRepairRankHeadersCommands.bank
      (raw sh rows ell p rho left count slots right src dst) := by
    rw [active_set_frame _ i hi,output_headers]
  have htraw : Placement.active headerPlacement target=ActiveRepairRankHeadersCommands.bank
      (raw sh rows ell p rho left count slots right src dst) := by
    rw [active_set_frame _ source source_numeric,hbraw]
  have htsource : target.head source=0 ∧ target.tape source=word := by simp only [target,setTape,Function.update_self,and_self]
  have htroles (j : Fin c) : target.head (roleTape j)=0 ∧ target.tape (roleTape j)=(fun _ => blank) := by
    have h := output_roles_blank selected j sh rows ell p rho left count slots right src dst v
    simpa only [target,b,setTape,Function.update_of_ne (source_role j).symm,Function.update_of_ne (hr j).symm] using h
  have ha := CompactComplexNonleafRoleMerge.active_input target
    (raw sh rows ell p rho left count slots right src dst) word (fun _ => fun _ => blank) htraw htsource htroles
  have he : Placement.extra CompactComplexNonleafRoleSplit.placement (target.append (SharedBank.empty 7 2))=
      Placement.extra CompactComplexNonleafRoleSplit.placement (b.append (SharedBank.empty 7 2)) := by
    dsimp only [target]
    rw [append_setTape,←source_active]
    exact extra_setTape_active _ _ _ _ _
  change Placement.combine CompactComplexNonleafRoleSplit.placement
    (CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
    (Placement.extra CompactComplexNonleafRoleSplit.placement (b.append (SharedBank.empty 7 2)))=
    target.append (SharedBank.empty 7 2)
  change Placement.active CompactComplexNonleafRoleSplit.placement (target.append (SharedBank.empty 7 2))=
    CompactNativeRoleOriginal.bank (raw sh rows ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c) at ha
  rw [←ha,←he,Placement.view]

/-- The literal actual child-role bank on the same permanent caller, ancestor
payload stack, reusable clock, and seven blank native merge work tapes. -/
def childBank (selected : Fin c) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hd : c ∣ rows/c) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ) :=
  Placement.replace CompactComplexNonleafRoleSplit.placement
    ((setTape (output selected sh rows ell p rho left count slots right src dst v) i advanced head).append
      (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f))

def program (selected : Fin c) := seq (CompactComplexNonleafRoleMerge.program s c)
  (extend (CompactComplexNonleafRoleReturn.program (s:=s) selected) 7)

def cost (selected : Fin c) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  CompactComplexNonleafRoleMerge.cost c sh rows ell p rho left count slots right src dst+1+
    CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell p rho left count slots right src dst

private theorem update_comm {t a : ℕ} (v : Tapes t a) (i j : Fin t) (hi : i≠j)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    setTape (setTape v i f p) j g q=setTape (setTape v j g q) i f p := by
  apply congrArg₂ Tapes.mk <;> funext k <;>
    by_cases hk : k=i <;> by_cases hj : k=j <;> simp_all [setTape]

/-- Actual arbitrary returned child roles physically merge and restore parent
rows, then the reverse generated-count boundary restores every parent/ancestor
payload frame while preserving the advanced controller word. This is strictly
physical: it makes no shared-grid or live-denominator semantic assertion. -/
theorem runs (selected : Fin c) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,(f j).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f j).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ)
    (hi : ∀ j,i≠numeric j) (hs : i≠stack) (hsourceSlot : i≠source)
    (hrslot : ∀ j,i≠roleTape j) (hclockSlot : i≠clock)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh rows ell p rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true) v) :
    HoareTime (program (s:=s) selected)
      (fun z => z=childBank selected sh rows ell p rho left count slots right src dst hd f v i advanced head)
      (fun z => z=(setTape (setTape v (roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) 0) i advanced head).append (SharedBank.empty 7 2))
      (cost (s:=s) selected sh rows ell p rho left count slots right src dst) := by
  let word := NativeZeroPadding.word (NativeZeroPaddingArray.word f)
  let b := childBank selected sh rows ell p rho left count slots right src dst hd f v i advanced head
  let ret := setTape (setTape (output selected sh rows ell p rho left count slots right src dst v) source word 0)
    i advanced head
  have ha : Placement.active CompactComplexNonleafRoleSplit.placement b=
      CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f) := Placement.active_replace _ _ _
  have hmerge := Placement.hoare_at
    (CompactComplexNonleafRoleMerge.local_runs c sh rows ell p rho left count slots right src dst
      hc hr hd hparent hG hA hK f hw) CompactComplexNonleafRoleSplit.placement b ha
  have hmerge' : HoareTime (CompactComplexNonleafRoleMerge.program s c)
      (fun z => z=b) (fun z => z=ret.append (SharedBank.empty 7 2))
      (CompactComplexNonleafRoleMerge.cost c sh rows ell p rho left count slots right src dst) := by
    refine hmerge.consequence (fun _ h => h) ?_ le_rfl
    rintro z ⟨u,rfl,rfl⟩
    dsimp only [b,childBank]
    simp only [Placement.replace,Placement.extra_combine]
    have he := parent_replacement selected sh rows ell p rho left count slots right src dst f v i advanced head hi hrslot
    dsimp only [Placement.replace] at he
    rw [he,update_comm _ i source hsourceSlot advanced word head 0]
  have hrows : 0<rows := by have hle := Nat.div_le_self rows c;omega
  have hreturn := CompactComplexNonleafRoleReturnFrame.return_result selected sh rows ell p rho left count slots right src dst
    v word i advanced head hi hs hsourceSlot hrslot hclockSlot hc hrows hr hG hA hK hraw hclock hsource hroles hfree
    (returned_supported sh rows ell p f hw)
  have hreturn' := hoare_extend_eq hreturn (SharedBank.empty 7 2)
  change HoareTime (extend (CompactComplexNonleafRoleReturn.program (s:=s) selected) 7)
    (fun z => z=ret.append (SharedBank.empty 7 2)) _ _ at hreturn'
  exact hmerge'.seq hreturn'

/-- A genuine next nonleaf descendant supplies the physical role divisors from
the already proved original padding geometry, without a callback or role oracle. -/
theorem descendant_runs (selected : Fin c) (sh : Shape)
    (m d K j ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (CompactGlobalRowPadding.rowsAt c m d K j/c) ell)
    (hw : ∀ k,(f k).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f k).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ)
    (hi : ∀ k,i≠numeric k) (hs : i≠stack) (hsourceSlot : i≠source)
    (hrslot : ∀ k,i≠roleTape k) (hclockSlot : i≠clock)
    (hc : 0<c) (hK : 0<K) (hj : j+1<CompactGlobalRowPadding.depth m d)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh (CompactGlobalRowPadding.rowsAt c m d K j) ell p rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c (CompactGlobalRowPadding.rowsAt c m d K j) ell p false))
    (hroles : ∀ k,v.head (roleTape k)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape k))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c (CompactGlobalRowPadding.rowsAt c m d K j) ell p true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c (CompactGlobalRowPadding.rowsAt c m d K j) ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c (CompactGlobalRowPadding.rowsAt c m d K j) ell p true) v) :
    HoareTime (program (s:=s) selected)
      (fun z => z=childBank selected sh (CompactGlobalRowPadding.rowsAt c m d K j)
        ell p rho left count slots right src dst (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).2
        f v i advanced head)
      (fun z => z=(setTape (setTape v (roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) 0) i advanced head).append (SharedBank.empty 7 2))
      (cost (s:=s) selected sh (CompactGlobalRowPadding.rowsAt c m d K j) ell p rho left count slots right src dst) :=
  runs selected sh _ ell p rho left count slots right src dst f hw v i advanced head hi hs hsourceSlot hrslot hclockSlot
    hc (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).1
    (CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj).2
    (CompactGlobalRowPadding.split_divides c m d K j hc hK (by omega))
    hG hA hchunk hraw hclock hsource hroles hfree

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturn
