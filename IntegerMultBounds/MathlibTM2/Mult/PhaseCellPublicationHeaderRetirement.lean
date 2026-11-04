module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Retire publication metadata after scatter, restoring the shared routing
suffix while preserving the ambient destination and retained caller masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def publicationMetadataVolume (src : Fin 13 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) A) : ℕ :=
  ((publicationHeaderCopies src).map (fun r => (S.R r.1).length)).sum

theorem publicationHeaderLoadCost_eq (src : Fin 13 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) :
    ((publicationHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1 =
      6*publicationMetadataVolume src S+79 := by
  simp [publicationHeaderCopies,publicationHeaderAssignments,publicationMetadataVolume]
  omega

theorem retirePublicationHeaders_exec_within
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q A U) (src : Fin 13 → Fin T)
    (k : Fin T) (ys : List (Fin (A+4)))
    (v : HS (T+PackedTranspose.tapeCount) Q A U) (S : Stacks (T+PackedTranspose.tapeCount) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let M := loadedPublicationHeaders src S
    let F : Stacks (T+PackedTranspose.tapeCount) A := {M with R := Function.update M.R (Fin.castAdd PackedTranspose.tapeCount k) ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords ((publicationHeaderCopies src).map Prod.snd)) (mk v F) (2*publicationMetadataVolume src S+27)
        (mk v' {S with R := Function.update S.R (Fin.castAdd PackedTranspose.tapeCount k) ys}) := by
  dsimp only
  let M := loadedPublicationHeaders src S
  let source := Fin.castAdd PackedTranspose.tapeCount k
  let F : Stacks (T+PackedTranspose.tapeCount) A := {M with R := Function.update M.R source ys}
  let regs := (publicationHeaderCopies src).map Prod.snd
  have hnd : regs.Nodup := by
    simp [regs,publicationHeaderCopies,publicationHeaderAssignments,List.nodup_cons,PackedTranspose.publicationReg_injective.eq_iff]
  have hoff (r) (hr : r ∈ publicationHeaderCopies src) : r.2 ≠ source := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (prefix_ne_routing k _).symm
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) regs hnd v F
  have hvolume : (regs.map (fun j => (F.R j).length)).sum = publicationMetadataVolume src S := by
    simp only [regs,List.map_map,publicationMetadataVolume]
    congr 1
    apply List.map_congr_left
    intro r hr
    change (F.R r.2).length = (S.R r.1).length
    rw [show F.R r.2 = M.R r.2 from Function.update_of_ne (hoff r hr) _ _]
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact congrArg List.length (loadedPublicationHeaders_read src S hblank p hp)
  have hlen : regs.length = 13 := by simp [regs,publicationHeaderCopies,publicationHeaderAssignments]
  rw [hvolume,hlen] at he
  have hend : {F with R := fun j => if j ∈ regs then [] else F.R j} = {S with R := Function.update S.R source ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ regs
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hj
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      have hne : Fin.natAdd T (PackedTranspose.publicationReg p.2) ≠ source := (prefix_ne_routing k _).symm
      simp only [if_pos hj,Function.update_of_ne hne,hblank _]
    · have hM : M.R j = S.R j := copyWordHeadersR_off S.R (publicationHeaderCopies src) S.R j
        (by intro r hr he; exact hj (List.mem_map.mpr ⟨r,hr,he⟩))
      simp [hj,F,hM,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [F,source,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
