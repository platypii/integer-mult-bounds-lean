module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposureHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Retire the copied exposure headers while preserving the caller output
source and restoring the initially fresh exposure suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def exposureMetadataVolume (src : Fin 8 → Fin T) (S : Stacks (T+175) A) : ℕ :=
  ((exposureHeaderCopies src).map (fun r => (S.R r.1).length)).sum

theorem exposureHeaderLoadCost_eq (src : Fin 8 → Fin T)
    (S : Stacks (T+175) A) :
    ((exposureHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1 =
      6*exposureMetadataVolume src S+49 := by
  simp [exposureHeaderCopies,exposureHeaderAssignments,exposureMetadataVolume]
  omega

theorem retireExposureHeaders_exec_within
    (body : P → Pr P (T+175) Q A U) (src : Fin 8 → Fin T)
    (k : Fin T) (ys : List (Fin (A+4)))
    (v : HS (T+175) Q A U) (S : Stacks (T+175) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let M := loadedExposureHeaders src S
    let F : Stacks (T+175) A := {M with R := Function.update M.R (Fin.castAdd 175 k) ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords ((exposureHeaderCopies src).map Prod.snd)) (mk v F) (2*exposureMetadataVolume src S+17)
        (mk v' {S with R := Function.update S.R (Fin.castAdd 175 k) ys}) := by
  dsimp only
  let M := loadedExposureHeaders src S
  let source := Fin.castAdd 175 k
  let F : Stacks (T+175) A := {M with R := Function.update M.R source ys}
  let regs := (exposureHeaderCopies src).map Prod.snd
  have hnd : regs.Nodup := by
    simp [regs,exposureHeaderCopies,exposureHeaderAssignments,List.nodup_cons,Fin.ext_iff,Fin.natAdd]
  have hoff (r) (hr : r ∈ exposureHeaderCopies src) : r.2 ≠ source := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (exposure_prefix_ne_private k _).symm
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) regs hnd v F
  have hvolume : (regs.map (fun j => (F.R j).length)).sum = exposureMetadataVolume src S := by
    simp only [regs,List.map_map,exposureMetadataVolume]
    congr 1
    apply List.map_congr_left
    intro r hr
    change (F.R r.2).length = (S.R r.1).length
    rw [show F.R r.2 = M.R r.2 from Function.update_of_ne (hoff r hr) _ _]
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact congrArg List.length (loadedExposureHeaders_read src S hblank p hp)
  have hlen : regs.length = 8 := by simp [regs,exposureHeaderCopies,exposureHeaderAssignments]
  rw [hvolume,hlen] at he
  have hend : {F with R := fun j => if j ∈ regs then [] else F.R j} = {S with R := Function.update S.R source ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ regs
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hj
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      have hne : Fin.natAdd T p.2 ≠ source := (exposure_prefix_ne_private k _).symm
      simp only [if_pos hj,Function.update_of_ne hne,hblank _]
    · have hM : M.R j = S.R j := copyWordHeadersR_off S.R (exposureHeaderCopies src) S.R j
        (by intro r hr he; exact hj (List.mem_map.mpr ⟨r,hr,he⟩))
      simp [hj,F,hM,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [F,source,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
