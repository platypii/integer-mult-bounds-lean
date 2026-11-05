module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportSlotBoundaryGeometry

/-! A structural list executor exports both controls for every boundary slot.
All metadata-readiness facts survive each exact two-port update. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type}

theorem boundarySeamCropSkip_injective : Function.Injective boundarySeamCropSkip := by decide +kernel

theorem boundarySeamCropSkip_ne_count (i j : Fin 3) : boundarySeamCropSkip i ≠ boundarySeamCropCount j := by
  revert i j
  decide +kernel

theorem boundarySeamCropPorts_lower (slot : Fin 3) :
    60 ≤ (boundarySeamCropSkip slot).val ∧ 60 ≤ (boundarySeamCropCount slot).val := by
  revert slot
  decide +kernel

def exportBoundaryGeometryState (s width w : ℕ) : List (Fin 3) → Stacks 117 A → Stacks 117 A
  | [],S => S
  | slot::slots,S => exportBoundaryGeometryState s width w slots
      {S with R := (Function.update (Function.update S.R (boundarySeamCropSkip slot)
        (List.replicate (coreStart width (boundaryCropIndex s width slot)*w) tick)) (boundarySeamCropCount slot)
        (List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick))}

theorem exportBoundaryGeometryState_off (s width w : ℕ) (slots : List (Fin 3)) (S : Stacks 117 A)
    (i : Fin 117) (hoff : ∀ slot ∈ slots, boundarySeamCropSkip slot ≠ i ∧ boundarySeamCropCount slot ≠ i) :
    (exportBoundaryGeometryState s width w slots S).R i = S.R i := by
  induction slots generalizing S with
  | nil => rfl
  | cons slot slots ih =>
    rw [exportBoundaryGeometryState,ih _ (fun j hj => hoff j (by simp [hj]))]
    dsimp only
    rw [Function.update_of_ne (hoff slot (by simp)).2.symm,
      Function.update_of_ne (hoff slot (by simp)).1.symm]

theorem exportBoundaryGeometryState_skip (s width w : ℕ) (slots : List (Fin 3)) (hnd : slots.Nodup)
    (S : Stacks 117 A) (slot : Fin 3) (hslot : slot ∈ slots) :
    (exportBoundaryGeometryState s width w slots S).R (boundarySeamCropSkip slot) =
      List.replicate (coreStart width (boundaryCropIndex s width slot)*w) tick := by
  induction slots generalizing S with
  | nil => simp at hslot
  | cons j slots ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hslot with rfl | hmem
    · rw [exportBoundaryGeometryState,exportBoundaryGeometryState_off s width w slots _ _ (by
        intro k hk
        refine ⟨?_,(boundarySeamCropSkip_ne_count slot k).symm⟩
        intro he
        exact hn.1 (boundarySeamCropSkip_injective he ▸ hk))]
      dsimp only
      rw [Function.update_of_ne (boundarySeamCropSkip_ne_count slot slot)]
      exact Function.update_self _ _ _
    · exact ih hn.2 _ hmem

theorem exportBoundaryGeometryState_count (s width w : ℕ) (slots : List (Fin 3)) (hnd : slots.Nodup)
    (S : Stacks 117 A) (slot : Fin 3) (hslot : slot ∈ slots) :
    (exportBoundaryGeometryState s width w slots S).R (boundarySeamCropCount slot) =
      List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick := by
  induction slots generalizing S with
  | nil => simp at hslot
  | cons j slots ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hslot with rfl | hmem
    · rw [exportBoundaryGeometryState,exportBoundaryGeometryState_off s width w slots _ _ (by
        intro k hk
        refine ⟨boundarySeamCropSkip_ne_count k slot,?_⟩
        intro he
        exact hn.1 (boundarySeamCropCount_injective he ▸ hk))]
      exact Function.update_self _ _ _
    · exact ih hn.2 _ hmem

theorem exportBoundaryGeometrySequence_exec (body : P → Pr P 117 Q A U)
    (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w)
    (hroom : 3*width < s) (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (slots : List (Fin 3)) (hnd : slots.Nodup) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hready : BoundaryCountReady D w value S)
    (hblank : ∀ slot ∈ slots, S.R (boundarySeamCropSkip slot) = [] ∧ S.R (boundarySeamCropCount slot) = [])
    (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (slots.map (fun slot => exportSlotBoundaryCountCost slot D s width w)).sum+1 ∧
      Exec body (restoringSequence exportSlotBoundaryGeometry slots) (mk v S) n
        (mk v' (exportBoundaryGeometryState s width w slots S)) := by
  induction slots generalizing v S with
  | nil => exact ⟨v,1,rfl,by simp,Exec.act _ _⟩
  | cons slot slots ih =>
    have hn := List.nodup_cons.mp hnd
    obtain ⟨u,a,hu,ha,he⟩ := exportSlotBoundaryGeometry_exec body slot D s width w hw hword hroom
      hvolumeFit value hvalues hfit v S hready.width hready.zero hready.words hready.tableBlank
      hready.masters hready.wide hready.tmp hready.saved (hblank slot (by simp)).1 (hblank slot (by simp)).2 depth
    let M : Stacks 117 A := {S with R := (Function.update (Function.update S.R (boundarySeamCropSkip slot)
      (List.replicate (coreStart width (boundaryCropIndex s width slot)*w) tick)) (boundarySeamCropCount slot)
      (List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick))}
    have hr : BoundaryCountReady D w value M := hready.of_frame D w value S M (by
      intro i hi
      have hb := boundarySeamCropPorts_lower slot
      have hs : i ≠ boundarySeamCropSkip slot := by intro heq; have hv := congrArg Fin.val heq; omega
      have hc : i ≠ boundarySeamCropCount slot := by intro heq; have hv := congrArg Fin.val heq; omega
      simp only [M,Function.update_of_ne hc,Function.update_of_ne hs])
    obtain ⟨v',b,hv,hb,hex⟩ := ih hn.2 u M hr (by
      intro j hj
      have hne : j ≠ slot := by intro h; subst j; exact hn.1 hj
      constructor
      · simpa only [M,Function.update_of_ne (boundarySeamCropSkip_ne_count j slot),
          Function.update_of_ne (boundarySeamCropSkip_injective.ne hne)] using (hblank j (by simp [hj])).1
      · simpa only [M,Function.update_of_ne (boundarySeamCropCount_injective.ne hne),
          Function.update_of_ne (boundarySeamCropSkip_ne_count slot j).symm] using (hblank j (by simp [hj])).2)
    refine ⟨v',a+b,hv.trans hu,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]; omega
    · exact Exec.seq he hex

theorem exportBoundaryGeometrySequence_native (slots : List (Fin 3)) :
    mnNativePushBound 3
      (restoringSequence (exportSlotBoundaryGeometry (P := P) (Q := Q) (A := A) (U := U)) slots) := by
  induction slots with
  | nil => exact Nat.zero_le _
  | cons slot slots ih => exact ⟨exportSlotBoundaryGeometry_native slot,ih⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
