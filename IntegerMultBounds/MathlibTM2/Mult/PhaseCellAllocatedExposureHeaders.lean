module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposureReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Load the six exposure headers and two counters from retained caller words.
The structural word copier preserves every caller source and both scratch ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
noncomputable section
variable {T Q A : ℕ} {P U : Type}

theorem exposure_prefix_ne_private (k : Fin T) (i : Fin 175) :
    (Fin.castAdd 175 k : Fin (T+175)) ≠ Fin.natAdd T i := by
  intro he
  have hv := congrArg (fun j : Fin (T+175) => j.val) he
  have hk := k.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def exposureHeaderAssignments : List (Fin 8 × Fin 175) :=
  [(0,145),(1,150),(2,152),(3,165),(4,163),(5,94),(6,168),(7,173)]

def exposureHeaderCopies (src : Fin 8 → Fin T) : List (Fin (T+175) × Fin (T+175)) :=
  exposureHeaderAssignments.map fun r => (Fin.castAdd 175 (src r.1),Fin.natAdd T r.2)

def loadExposureHeaders (src : Fin 8 → Fin T) : Pr P (T+175) Q A U :=
  copyWordHeaders (Fin.natAdd T 166) (Fin.natAdd T 167) (exposureHeaderCopies src)

def loadedExposureHeaders (src : Fin 8 → Fin T) (S : Stacks (T+175) A) :=
  {S with R := copyWordHeadersR S.R (exposureHeaderCopies src) S.R}

theorem loadedExposureHeaders_read (src : Fin 8 → Fin T)
    (S : Stacks (T+175) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (r : Fin 8 × Fin 175) (hr : r ∈ exposureHeaderAssignments) :
    (loadedExposureHeaders src S).R (Fin.natAdd T r.2) =
      S.R (Fin.castAdd 175 (src r.1)) := by
  have hnd : ((exposureHeaderCopies src).map Prod.snd).Nodup := by
    simp [exposureHeaderCopies,exposureHeaderAssignments,List.nodup_cons,Fin.ext_iff,Fin.natAdd]
  have hh := copyWordHeadersR_get S.R (exposureHeaderCopies src) hnd S.R
    (Fin.castAdd 175 (src r.1),Fin.natAdd T r.2) (List.mem_map.mpr ⟨r,hr,rfl⟩)
  simpa only [loadedExposureHeaders,hblank _,List.append_nil] using hh

theorem loadExposureHeaders_exec_within
    (body : P → Pr P (T+175) Q A U) (src : Fin 8 → Fin T)
    (v : HS (T+175) Q A U) (S : Stacks (T+175) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let cost := ((exposureHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost) depth
        (loadExposureHeaders src) (mk v S) cost (mk v' (loadedExposureHeaders src S)) ∧
      (∀ r ∈ exposureHeaderAssignments, (loadedExposureHeaders src S).R (Fin.natAdd T r.2) =
        S.R (Fin.castAdd 175 (src r.1))) ∧
      (∀ k : Fin T, (loadedExposureHeaders src S).R (Fin.castAdd 175 k) = S.R (Fin.castAdd 175 k)) := by
  dsimp only
  have hni : Function.Injective (Fin.natAdd T : Fin 175 → Fin (T+175)) := by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    simp only [Fin.val_natAdd] at hv
    omega
  have hd := hni
  have hregs : ∀ r ∈ exposureHeaderCopies src,
      [r.1,r.2,Fin.natAdd T 166,Fin.natAdd T 167].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have htmp : p.2 ≠ 166 := by
      simp only [exposureHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hsaved : p.2 ≠ 167 := by
      simp only [exposureHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [List.nodup_cons,exposure_prefix_ne_private,hd.eq_iff,htmp,hsaved]
  have hsep : ∀ r ∈ exposureHeaderCopies src, ∀ p ∈ exposureHeaderCopies src, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hp
    exact (exposure_prefix_ne_private _ _).symm
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) (Fin.natAdd T 166)
    (Fin.natAdd T 167) (exposureHeaderCopies src) hregs hsep S.R v S (by intros; rfl)
    (hblank _) (hblank _)
  refine ⟨v',hu,mn_native_exec_within he 2 (copyWordHeaders_native _ _ _) depth _ (by omega),?_,?_⟩
  · exact loadedExposureHeaders_read src S hblank
  · intro k
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (exposure_prefix_ne_private _ _).symm


end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
