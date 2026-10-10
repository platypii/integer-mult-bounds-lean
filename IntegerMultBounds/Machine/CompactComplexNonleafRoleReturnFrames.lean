import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrame

/-! Arbitrary simultaneous controller changes at a physical nonleaf return.
Only the raw numeric bank, payloads, payload stack and reusable clock are
protected. All complementary tapes and heads may come from an unrelated bank. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrames
noncomputable section
open CompactComplexNonleafRoleEntry
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

/-- Slots needed to execute the genuine generated-count payload return. -/
def Core (i : Fin (tapes s c)) : Prop :=
  (∃ j : Fin 43, i = numeric j) ∨ i = source ∨
    (∃ j : Fin c, i = roleTape j) ∨ i = stack ∨ i = clock

/-- Replace every complementary controller tape and head simultaneously. -/
def framed (v w : Tapes (tapes s c) 2) : Tapes (tapes s c) 2 := by
  classical
  exact ⟨fun i => if Core i then v.head i else w.head i,
    fun i => if Core i then v.tape i else w.tape i⟩

theorem framed_core (v w : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (hi : Core i) :
    (framed v w).head i = v.head i ∧ (framed v w).tape i = v.tape i := by
  simp [framed, hi]

theorem framed_complement (v w : Tapes (tapes s c) 2) (i : Fin (tapes s c))
    (hi : ¬ Core i) :
    (framed v w).head i = w.head i ∧ (framed v w).tape i = w.tape i := by
  simp [framed, hi]

/-- Identify an actual child-return bank by checking only protected endpoints;
its entire complementary state supplies its own frame. -/
theorem framed_eq_of_core (v w : Tapes (tapes s c) 2)
    (hhead : ∀ i, Core i → v.head i = w.head i)
    (htape : ∀ i, Core i → v.tape i = w.tape i) : framed v w = w := by
  classical
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : Core i
  · exact (framed_core v w i hi).1.trans (hhead i hi)
  · exact (framed_complement v w i hi).1
  · exact (framed_core v w i hi).2.trans (htape i hi)
  · exact (framed_complement v w i hi).2

theorem framed_framed (v u w : Tapes (tapes s c) 2) :
    framed (framed v u) w = framed v w := by
  classical
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [framed] <;> split_ifs <;> rfl

private theorem core_numeric (j : Fin 43) : Core (numeric (s:=s) (c:=c) j) :=
  Or.inl ⟨j, rfl⟩
private theorem core_source : Core (source (s:=s) (c:=c)) := Or.inr (Or.inl rfl)
private theorem core_role (j : Fin c) : Core (roleTape (s:=s) j) :=
  Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))
private theorem core_stack : Core (stack (s:=s) (c:=c)) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))
private theorem core_clock : Core (clock (s:=s) (c:=c)) :=
  Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem framed_setTape (v w : Tapes (tapes s c) 2) (i : Fin (tapes s c))
    (hi : Core i) (f : ℤ → Fin 6) (p : ℤ) :
    framed (setTape v i f p) w = setTape (framed v w) i f p := by
  classical
  apply congrArg₂ Tapes.mk <;> funext j <;>
    by_cases hj : j = i <;> simp_all [framed, setTape]

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c) (Fin.castAdd (tapes s c-43) i) = numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

theorem framed_headers (v w : Tapes (tapes s c) 2) :
    Placement.active headerPlacement (framed v w) = Placement.active headerPlacement v := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [numeric_active]
  · exact (framed_core v w _ (core_numeric i)).1
  · exact (framed_core v w _ (core_numeric i)).2

private theorem saved_framed
    (ops : List (RoleArrayFrames.Role (layout (s:=s) (c:=c))))
    (hr : ∀ r ∈ ops, Core r.val) (n : ℕ) (v w : Tapes (tapes s c) 2) :
    RoleArrayFrames.saved layout ops n (framed v w) =
      framed (RoleArrayFrames.saved layout ops n v) w := by
  induction ops generalizing v with
  | nil => rfl
  | cons r ops ih =>
    have hrole := framed_core v w r.val (hr r List.mem_cons_self)
    have hstack := framed_core v w stack core_stack
    have hsave : RoleArrayFrames.saveOne layout r n (framed v w) =
        framed (RoleArrayFrames.saveOne layout r n v) w := by
      simp only [RoleArrayFrames.saveOne, RoleArrayStackAt.pushed,
        RoleArrayFrames.slots, layout, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hrole.2, hstack.1, hstack.2,
        framed_setTape _ w stack core_stack,
        framed_setTape _ w r.val (hr r List.mem_cons_self)]
    change RoleArrayFrames.saved layout ops n
      (RoleArrayFrames.saveOne layout r n (framed v w)) = _
    rw [hsave, ih (by intro r h; exact hr r (List.mem_cons_of_mem _ h))]
    rfl

theorem parked_framed (selected : Fin c) (n : ℕ) (v w : Tapes (tapes s c) 2) :
    parked selected n (framed v w) = framed (parked selected n v) w := by
  unfold parked RoleArrayCall.entered
  rw [saved_framed _ (by
    intro r hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp hr).1
    exact core_role j)]
  simp only [RoleArrayMove.moved, RoleArrayCall.slots, Matrix.cons_val_zero,
    Matrix.cons_val_one, role, sourceRole]
  rw [(framed_core _ w _ (core_role selected)).2,
    framed_setTape _ w _ core_source,
    framed_setTape _ w _ (core_role selected)]

/-- Entry reads and changes only the protected payload bank. -/
theorem output_framed (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (v w : Tapes (tapes s c) 2)
    (hraw : Placement.active headerPlacement v = ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)) :
    output selected sh rows ell metadataP rho left count slots right src dst (framed v w) =
      framed (output selected sh rows ell metadataP rho left count slots right src dst v) w := by
  rw [CompactComplexNonleafRoleReturn.output_eq selected sh rows ell metadataP rho left count slots
      right src dst _ ((framed_headers v w).trans hraw),
    CompactComplexNonleafRoleReturn.output_eq selected sh rows ell metadataP rho left count slots
      right src dst v hraw,
    saved_framed _ (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact core_source), parked_framed]

/-- Genuine payload recovery preserves the entire arbitrary complementary bank.
Readiness is derived from the original raw bank and payload frame, rather than
assumed for a separately prepared return input. -/
theorem return_result (selected : Fin c) (sh : CompactGadgetReservationShape.Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (v w : Tapes (tapes s c) 2) (returned : ℤ → Fin 6)
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
      (fun z => z=framed
        (setTape (output selected sh rows ell metadataP rho left count slots right src dst v)
          source returned 0) w)
      (fun z => z=framed (setTape v (roleTape selected) returned 0) w)
      (CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell metadataP rho left count slots
        right src dst) := by
  have hclock' : (framed v w).head clock=0 ∧ (framed v w).tape clock=(fun _ => blank) := by
    rw [(framed_core v w _ core_clock).1, (framed_core v w _ core_clock).2]
    exact hclock
  have hsource' : (framed v w).head source=0 ∧ RoleArrayStack.Supported ((framed v w).tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false) := by
    rw [(framed_core v w _ core_source).1, (framed_core v w _ core_source).2]
    exact hsource
  have hroles' (j : Fin c) : (framed v w).head (roleTape j)=0 ∧
      RoleArrayStack.Supported ((framed v w).tape (roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) := by
    rw [(framed_core v w _ (core_role j)).1, (framed_core v w _ (core_role j)).2]
    exact hroles j
  have hfree' : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell metadataP true) (framed v w) := by
    unfold CompactComplexNonleafRoleReturn.Free
    rw [(framed_core v w _ core_stack).1, (framed_core v w _ core_stack).2]
    exact hfree
  have h := CompactComplexNonleafRoleReturn.runs_result (s:=s) selected sh rows ell metadataP rho left
    count slots right src dst (framed v w) returned hc hr hgroup hG hA hK
    ((framed_headers v w).trans hraw) hclock' hsource' hroles' hfree' hreturned
  rw [output_framed selected sh rows ell metadataP rho left count slots right src dst v w hraw,
    ← framed_setTape _ w source core_source,
    ← framed_setTape _ w (roleTape selected) (core_role selected)] at h
  exact h

/-- Every inherited permanent storage slot lies in the unrestricted frame. -/
theorem old_slot_complement (j : Fin s) :
    ¬ Core (CompactComplexNonleafRoleReturnFrame.oldSlot (c:=c) j) := by
  obtain ⟨hn, hs, hsource, hr, hclock⟩ :=
    CompactComplexNonleafRoleReturnFrame.old_slot_disjoint (c:=c) j
  rintro (⟨k, hk⟩ | hk | ⟨k, hk⟩ | hk | hk)
  · exact hn k hk
  · exact hsource hk
  · exact hr k hk
  · exact hs hk
  · exact hclock hk

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrames
