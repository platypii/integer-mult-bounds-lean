module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! The generated binary dimensions are owned metadata. Retire them after the
restoring publication call, leaving only its source and output changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

theorem retirePublicationBinaryHeaders_exec_within
    (body : P → Pr P tapeCount Q (prime+K) U) (a b C V : ℕ)
    (src dst : Fin tapeCount) (hsrc : src ∉ publicationBinaryRegisters) (hdst : dst ∉ publicationBinaryRegisters)
    (xs ys : List (Fin (prime+K+4))) (S : Stacks tapeCount (prime+K))
    (hblank : ∀ i ∈ publicationBinaryRegisters, S.R i = [])
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) :
    let M := publicationHeadersState a b C V S
    let F := {M with R := Function.update (Function.update M.R src xs) dst ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords publicationBinaryRegisters) (mk v F) (6*V+7)
        (mk v' {S with R := Function.update (Function.update S.R src xs) dst ys}) := by
  dsimp only
  let M := publicationHeadersState a b C V S
  let F := {M with R := Function.update (Function.update M.R src xs) dst ys}
  have hnd : publicationBinaryRegisters.Nodup := by
    simp [publicationBinaryRegisters,List.nodup_cons,headerReg_injective.eq_iff]
  have hread (i) (hi : i ∈ publicationBinaryRegisters) : F.R i = M.R i := by
    have hs : i ≠ src := by intro he; exact hsrc (he ▸ hi)
    have hd : i ≠ dst := by intro he; exact hdst (he ▸ hi)
    exact (Function.update_of_ne hd _ _).trans (Function.update_of_ne hs _ _)
  have hsize (i) (hi : i ∈ publicationBinaryRegisters) : (F.R i).length = V := by
    rw [hread i hi]
    simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [M,publicationHeadersState,headerReg_injective.eq_iff,length_binSyms]
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) publicationBinaryRegisters hnd v F
  have hcost : 2*(publicationBinaryRegisters.map (fun r => (F.R r).length)).sum+
      2*publicationBinaryRegisters.length+1 = 6*V+7 := by
    have h97 := hsize (headerReg 97) (by simp [publicationBinaryRegisters])
    have h98 := hsize (headerReg 98) (by simp [publicationBinaryRegisters])
    have h102 := hsize (headerReg 102) (by simp [publicationBinaryRegisters])
    simp [publicationBinaryRegisters,h97,h98,h102]
    omega
  rw [hcost] at he
  have hend : ({F with R := fun i => if i ∈ publicationBinaryRegisters then [] else F.R i} : Stacks tapeCount (prime+K)) =
      {S with R := Function.update (Function.update S.R src xs) dst ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i ∈ publicationBinaryRegisters
    · have hs : i ≠ src := by intro he; exact hsrc (he ▸ hi)
      have hd : i ≠ dst := by intro he; exact hdst (he ▸ hi)
      simp only [if_pos hi,Function.update_of_ne hd,Function.update_of_ne hs,hblank i hi]
    · have hM : M.R i = S.R i := by
        simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
        simp only [M,publicationHeadersState,Function.update_of_ne hi.2.2,Function.update_of_ne hi.2.1,Function.update_of_ne hi.1]
      simp [hi,F,Function.update_apply,hM]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by dsimp only [F,M]; omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
