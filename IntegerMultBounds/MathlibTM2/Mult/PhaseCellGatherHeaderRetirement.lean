module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedGatherHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Retire the copied routing headers while preserving the numerical supplier
source and restoring the initially fresh routing suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def gatherMetadataVolume (src : Fin 7 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) : ℕ :=
  ((gatherHeaderCopies src).map (fun r => (S.R r.1).length)).sum

theorem gatherHeaderLoadCost_eq (src : Fin 7 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) :
    ((gatherHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1 =
      6*gatherMetadataVolume src S+49 := by
  simp [gatherHeaderCopies,gatherHeaderAssignments,gatherMetadataVolume]
  omega

theorem retireGatherHeaders_exec_within
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U) (src : Fin 7 → Fin T)
    (k : Fin T) (ys : List (Fin (prime+K+4)))
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let M := loadedGatherHeaders src S
    let F : Stacks (T+PackedTranspose.tapeCount) (prime+K) := {M with R := Function.update M.R (Fin.castAdd PackedTranspose.tapeCount k) ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords ((gatherHeaderCopies src).map Prod.snd)) (mk v F) (2*gatherMetadataVolume src S+17)
        (mk v' {S with R := Function.update S.R (Fin.castAdd PackedTranspose.tapeCount k) ys}) := by
  dsimp only
  let M := loadedGatherHeaders src S
  let source := Fin.castAdd PackedTranspose.tapeCount k
  let F : Stacks (T+PackedTranspose.tapeCount) (prime+K) := {M with R := Function.update M.R source ys}
  let regs := (gatherHeaderCopies src).map Prod.snd
  have hnd : regs.Nodup := by
    simp [regs,gatherHeaderCopies,gatherHeaderAssignments,List.nodup_cons,headerReg_injective.eq_iff]
  have hoff (r) (hr : r ∈ gatherHeaderCopies src) : r.2 ≠ source := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (prefix_ne_routing k _).symm
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) regs hnd v F
  have hvolume : (regs.map (fun j => (F.R j).length)).sum = gatherMetadataVolume src S := by
    simp only [regs,List.map_map,gatherMetadataVolume]
    congr 1
    apply List.map_congr_left
    intro r hr
    change (F.R r.2).length = (S.R r.1).length
    rw [show F.R r.2 = M.R r.2 from Function.update_of_ne (hoff r hr) _ _]
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact congrArg List.length (loadedGatherHeaders_read src S hblank p hp)
  have hlen : regs.length = 8 := by simp [regs,gatherHeaderCopies,gatherHeaderAssignments]
  rw [hvolume,hlen] at he
  have hend : {F with R := fun j => if j ∈ regs then [] else F.R j} = {S with R := Function.update S.R source ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ regs
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hj
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      have hne : Fin.natAdd T (headerReg p.2) ≠ source := (prefix_ne_routing k _).symm
      simp only [if_pos hj,Function.update_of_ne hne,hblank _]
    · have hM : M.R j = S.R j := copyWordHeadersR_off S.R (gatherHeaderCopies src) S.R j
        (by intro r hr he; exact hj (List.mem_map.mpr ⟨r,hr,he⟩))
      simp [hj,F,hM,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [F,source,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
