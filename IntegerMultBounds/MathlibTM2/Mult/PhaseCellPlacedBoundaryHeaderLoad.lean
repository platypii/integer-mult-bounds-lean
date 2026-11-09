module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady

/-! Load boundary controls from retained masters in any caller layout. Sources
may be shared; one restoring copy loop fills the eleven distinct destinations. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s : ℕ} {P U : Type}

def placedBoundaryHeaderPairs (e : Fin 117 → Fin T) (masters : Fin 11 → Fin T) :=
  List.ofFn (fun i => (masters i,e (boundarySeamMasterRole i)))

def placedBoundaryHeaderLoad (e : Fin 117 → Fin T) (masters : Fin 11 → Fin T) : Pr P T Q A U :=
  copyWordHeaders (e 27) (e 28) (placedBoundaryHeaderPairs e masters)

theorem placedBoundaryHeaderLoad_exec_within (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (masters : Fin 11 → Fin T)
    (hsep : ∀ i, ∀ r ∈ List.ofFn boundarySeamMasterRole++[27,28], masters i ≠ e r)
    (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : BoundarySeamHeaderWords (s := s) p width W D N seedValue (fun i => S.R (masters i)))
    (hblank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R (e i) = []) (depth : ℕ) :
    let pairs := placedBoundaryHeaderPairs e masters
    let F : Stacks T A := {S with R := copyWordHeadersR S.R pairs S.R}
    let cost := (pairs.map (fun r => 6*(S.R r.1).length+6)).sum+1
    ∃ v', v'.user = v.user ∧
      BoundarySeamReady (s := s) p width W D N boundarySeamCropCount seedValue (embStk e F) ∧
      (∀ i, F.R (e (boundarySeamMasterRole i)) = S.R (masters i)) ∧
      (∀ i, (∀ j, e (boundarySeamMasterRole j) ≠ i) → F.R i = S.R i) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+2*cost) depth
        (placedBoundaryHeaderLoad e masters) (mk v S) cost (mk v' F) := by
  dsimp only
  have hrole (i : Fin 11) : boundarySeamMasterRole i ≠ 27 ∧ boundarySeamMasterRole i ≠ 28 := by
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.2.2
  have hdestBlank (i : Fin 11) : S.R (e (boundarySeamMasterRole i)) = [] := by
    have hb : ∀ i, (boundarySeamMasterRole i).val < 63 := by decide +kernel
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact hblank _ (hb i) h.1 h.2.1
  obtain ⟨v',hu,hex⟩ := copyWordHeaders_exec (body := body) (e 27) (e 28) (placedBoundaryHeaderPairs e masters)
    (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
      exact ⟨⟨hsep i _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)),
        hsep i 27 (by simp),hsep i 28 (by simp)⟩,
        ⟨he.ne (hrole i).1,he.ne (hrole i).2⟩,he.ne (by decide)⟩)
    (by
      intro r hr q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
      exact (hsep j _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))).symm)
    S.R v S (by intro r hr; rfl)
    (hblank 27 (by decide) (by decide) (by decide)) (hblank 28 (by decide) (by decide) (by decide))
  let F : Stacks T A := {S with R := copyWordHeadersR S.R (placedBoundaryHeaderPairs e masters) S.R}
  have hget (i : Fin 11) : F.R (e (boundarySeamMasterRole i)) = S.R (masters i) := by
    have hnd : ((placedBoundaryHeaderPairs e masters).map Prod.snd).Nodup := by
      rw [placedBoundaryHeaderPairs,List.map_ofFn]
      exact List.nodup_ofFn.mpr (he.comp boundarySeamMasterRole_injective)
    have h := copyWordHeadersR_get S.R (placedBoundaryHeaderPairs e masters) hnd S.R _
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [hdestBlank i,List.append_nil] using h
  have hframe (i : Fin T) (hi : ∀ j, e (boundarySeamMasterRole j) ≠ i) : F.R i = S.R i := by
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi j
  refine ⟨v',hu,BoundarySeamReady.of_header_frame p width W D N seedValue _ hwords e he S F
    hblank hget hframe,hget,hframe,?_⟩
  exact mn_native_exec_within hex 2 (copyWordHeaders_native _ _ _) depth _ (le_refl _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
