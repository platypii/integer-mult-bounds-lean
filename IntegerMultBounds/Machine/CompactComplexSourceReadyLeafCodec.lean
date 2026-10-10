import IntegerMultBounds.Machine.CompactComplexSourceReadyLeafPhase

/-! The source-ready leaf physically synthesizes its polynomial codec payload
and baseline precision from retained raw metadata, then restores both. Numeric
placement preserves the actual source, vacant roles and arbitrary controller. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyLeafCodec
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexNonleafRoleEntry (numeric headerPlacement)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexSourceReadyLeafPhase (publicTapes privateTapes source ready)
open SharedPlacementAlphabet (setTape)
open ActiveRepairRankHeadersCommands (State bank)
variable {s c : ℕ}

def slot (i : Fin 43) : Fin (publicTapes s c) := Fin.castAdd 7 (numeric i)
private theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [slot,numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def placement := InjectivePlacement.placement (slot (s:=s) (c:=c)) slot_injective
  (by unfold publicTapes CompactComplexNonleafRoleSourceReturn.tapes CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes; omega : 43+(publicTapes s c-43)=publicTapes s c)

def numericProgram {q : ℕ} (M : Program 43 q 2) :=
  Placement.placed M (placement (s:=s) (c:=c))
def headers (v : Tapes (publicTapes s c) 2) (st : State) := Placement.replace placement v (bank st)

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c)
      (Fin.castAdd (CompactComplexNonleafRoleEntry.tapes s c-43) i)=numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

theorem active (v : Tapes (publicTapes s c) 2) :
    Placement.active placement v=Placement.active headerPlacement (base v) := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [placement,InjectivePlacement.active_slot,slot,numeric_active,base]

theorem headers_active (v : Tapes (publicTapes s c) 2) (st : State) :
    Placement.active headerPlacement (base (headers v st))=bank st := by
  rw [←active]
  exact Placement.active_replace _ _ _

theorem numeric_runs {q : ℕ} (M : Program 43 q 2)
    (v : Tapes (publicTapes s c) 2) (st su : State) (time : ℕ)
    (hv : Placement.active headerPlacement (base v)=bank st)
    (h : HoareTime M (fun z => z=bank st) (fun z => z=bank su) time) :
    HoareTime (numericProgram M) (fun z => z=v) (fun z => z=headers v su) time := by
  have hh := Placement.hoare_at h placement v ((active v).trans hv)
  exact hh.consequence (fun _ hz => hz) (fun _ hz => by rcases hz with ⟨w,rfl,rfl⟩;rfl) le_rfl

private theorem replace_frame {n u t a : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes n a) (i : Fin t)
    (hi : ∀ j,i≠e (Fin.castAdd u j)) :
    (Placement.replace e v small).head i=v.head i ∧
    (Placement.replace e v small).tape i=v.tape i := by
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases with
  | left j => exact False.elim (hi j rfl)
  | right j => simp [Placement.replace,Placement.extra]

private theorem source_outside (i : Fin 43) : source (s:=s) (c:=c)≠slot i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [source,slot,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem headers_source (v : Tapes (publicTapes s c) 2) (st : State) :
    (headers v st).head source=v.head source ∧ (headers v st).tape source=v.tape source :=
  replace_frame placement v _ source (by intro j;simpa only [placement,InjectivePlacement.active_slot] using source_outside j)

theorem headers_frame (v : Tapes (publicTapes s c) 2) (st : State) (i : Fin (publicTapes s c))
    (hi : ∀ j,i≠slot j) :
    (headers v st).head i=v.head i ∧ (headers v st).tape i=v.tape i :=
  replace_frame placement v _ i (by intro j;simpa only [placement,InjectivePlacement.active_slot] using hi j)

theorem headers_headers (v : Tapes (publicTapes s c) 2) (st su : State) :
    headers (headers v st) su=headers v su := by
  unfold headers Placement.replace
  rw [Placement.extra_combine]

private theorem replace_setTape {n u t a : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes n a) (i : Fin t)
    (hi : ∀ j,i≠e (Fin.castAdd u j)) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e (setTape v i f p) small=setTape (Placement.replace e v small) i f p := by
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases with
  | left j => exact False.elim (hi j rfl)
  | right j =>
    apply congrArg₂ Tapes.mk <;> funext k
    all_goals obtain ⟨k,rfl⟩ := e.surjective k
    all_goals induction k using Fin.addCases with
    | left k =>
      have hn : e (Fin.castAdd u k)≠e (Fin.natAdd n j) := by
        intro h;have hv := congrArg Fin.val (e.injective h);simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
      simp [Placement.replace,Placement.combine,Tapes.reindex,Tapes.append,setTape,hn]
    | right k =>
      by_cases hk : k=j
      · subst k; simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape]
      · have hn : e (Fin.natAdd n k)≠e (Fin.natAdd n j) := fun h => hk (Fin.natAdd_injective _ _ (e.injective h))
        simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape,hn]

theorem headers_set_source (v : Tapes (publicTapes s c) 2) (st : State) (f : ℤ → Fin 6) :
    headers (setTape v source f 0) st=setTape (headers v st) source f 0 :=
  replace_setTape placement v _ source (by intro j;simpa only [placement,InjectivePlacement.active_slot] using source_outside j) f 0

theorem headers_original (v : Tapes (publicTapes s c) 2) (st : State)
    (hv : Placement.active headerPlacement (base v)=bank st) : headers v st=v := by
  unfold headers
  rw [←hv,←active]
  exact Placement.replace_active _ _

theorem active_set_source (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) :
    Placement.active headerPlacement (base (setTape v source f 0))=
      Placement.active headerPlacement (base v) := by
  rw [←active,←active]
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [placement,InjectivePlacement.active_slot,setTape,
      Function.update_of_ne (source_outside i).symm]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyLeafCodec
