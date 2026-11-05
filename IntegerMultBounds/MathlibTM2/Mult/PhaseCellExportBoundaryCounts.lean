module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportSlotBoundaryCount

/-! Generate a list of distinct crop controls through one restored metadata bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type}

structure BoundaryCountReady (D w : ℕ) (value : Fin 117 → ℕ) (S : Stacks 117 A) : Prop where
  width : (S.R 58).length = D
  zero : S.R 59 = []
  words : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j))
  tableBlank : ∀ r, S.R (boundaryCounterRegister r) = []
  masters : S.R 26 = [] ∧ S.R 24 = []
  wide : (S.R 17).length = w
  tmp : S.R 27 = []
  saved : S.R 28 = []

theorem BoundaryCountReady.of_frame (D w : ℕ) (value : Fin 117 → ℕ) (S M : Stacks 117 A)
    (h : BoundaryCountReady D w value S) (hread : ∀ i : Fin 117, i.val < 60 → M.R i = S.R i) :
    BoundaryCountReady D w value M := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hread 58 (by decide)] using h.width
  · simpa only [hread 59 (by decide)] using h.zero
  · intro j
    rw [hread _ (by fin_cases j <;> decide)]
    exact h.words j
  · intro r
    rw [hread _ ((boundaryCounterRegister_bounds r).2.trans_le (by decide))]
    exact h.tableBlank r
  · simpa only [hread 26 (by decide),hread 24 (by decide)] using h.masters
  · simpa only [hread 17 (by decide)] using h.wide
  · simpa only [hread 27 (by decide)] using h.tmp
  · simpa only [hread 28 (by decide)] using h.saved

def exportBoundaryCountsState (s width w : ℕ) : List (Fin 3) → Stacks 117 A → Stacks 117 A
  | [],S => S
  | slot::slots,S => exportBoundaryCountsState s width w slots
      {S with R := (Function.update S.R (boundarySeamCropCount slot)
        (List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick))}

theorem boundarySeamCropCount_injective : Function.Injective boundarySeamCropCount := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [boundarySeamCropCount,Fin.val_mk] at hv
  omega

theorem exportBoundaryCountsState_off (s width w : ℕ) (slots : List (Fin 3))
    (S : Stacks 117 A) (i : Fin 117)
    (hoff : ∀ slot ∈ slots, boundarySeamCropCount slot ≠ i) :
    (exportBoundaryCountsState s width w slots S).R i = S.R i := by
  induction slots generalizing S with
  | nil => rfl
  | cons slot slots ih =>
    rw [exportBoundaryCountsState,ih _ (fun j hj => hoff j (by simp [hj]))]
    exact Function.update_of_ne (hoff slot (by simp)).symm _ _

theorem exportBoundaryCountsState_get (s width w : ℕ) (slots : List (Fin 3))
    (hnd : slots.Nodup) (S : Stacks 117 A) (slot : Fin 3) (hslot : slot ∈ slots) :
    (exportBoundaryCountsState s width w slots S).R (boundarySeamCropCount slot) =
      List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick := by
  induction slots generalizing S with
  | nil => simp at hslot
  | cons j slots ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hslot with rfl | hmem
    · rw [exportBoundaryCountsState,exportBoundaryCountsState_off s width w slots _ _ (by
        intro k hk he
        exact hn.1 (boundarySeamCropCount_injective he ▸ hk))]
      exact Function.update_self _ _ _
    · exact ih hn.2 _ hmem

theorem exportBoundaryCounts_exec (body : P → Pr P 117 Q A U)
    (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w)
    (hroom : 3*width < s) (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (slots : List (Fin 3)) (hnd : slots.Nodup) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hready : BoundaryCountReady D w value S)
    (hblank : ∀ slot ∈ slots, S.R (boundarySeamCropCount slot) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (slots.map (fun slot => exportSlotBoundaryCountCost slot D s width w)).sum+1 ∧
      Exec body (restoringSequence exportSlotBoundaryCount slots) (mk v S) n
        (mk v' (exportBoundaryCountsState s width w slots S)) := by
  induction slots generalizing v S with
  | nil => exact ⟨v,1,rfl,by simp,Exec.act _ _⟩
  | cons slot slots ih =>
    have hn := List.nodup_cons.mp hnd
    obtain ⟨u,a,hu,ha,he⟩ := exportSlotBoundaryCount_exec body slot D s width w hw hword hroom
      hvolumeFit value hvalues hfit v S hready.width hready.zero hready.words hready.tableBlank
      hready.masters hready.wide hready.tmp hready.saved (hblank slot (by simp)) depth
    let M : Stacks 117 A := {S with R := (Function.update S.R (boundarySeamCropCount slot)
      (List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick))}
    have hr : BoundaryCountReady D w value M := hready.of_frame D w value S M (by
      intro i hi
      apply Function.update_of_ne
      intro heq
      have hv := congrArg Fin.val heq
      simp only [boundarySeamCropCount,Fin.val_mk] at hv
      omega)
    obtain ⟨v',b,hv,hb,hex⟩ := ih hn.2 u M hr (by
      intro j hj
      have hne : j ≠ slot := by intro h; subst j; exact hn.1 hj
      rw [show M.R (boundarySeamCropCount j) = S.R (boundarySeamCropCount j) from
        Function.update_of_ne (boundarySeamCropCount_injective.ne hne) _ _]
      exact hblank j (by simp [hj]))
    refine ⟨v',a+b,hv.trans hu,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · exact Exec.seq he hex

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
