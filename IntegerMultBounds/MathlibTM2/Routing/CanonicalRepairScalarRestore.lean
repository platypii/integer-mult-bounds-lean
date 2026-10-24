module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairOperandReady
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Clear the six new repair operands, retaining all preceding header metadata
and a disjoint caller output. No input word is among the erased registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairScalarSlots : List (Fin 130) := [121,122,124,125,126,127]

theorem canonicalRepairScalarCleanCost (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n r B : ℕ) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    metadataCleanCost (canonicalRepairBlockGeneratedBank R rg L n r B)
      (canonicalRepairScalarSlots.map rg) =
      2*(p.wc+p.wy+(n+1)+canonicalScalarWidth (n+1)+canonicalScalarWidth B+
        canonicalScalarWidth (n+B+1))+13 := by
  simp [metadataCleanCost,canonicalRepairScalarSlots,canonicalRepairBlockGeneratedBank,
    canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,
    repairZeroBank,canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,
    canonicalRepairZeroCore,canonicalRepairZeroSlot,Function.comp_def,hrg.eq_iff,length_binSyms]
  omega

theorem canonicalRepairBlockGeneratedBank_restore (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n r B : ℕ)
    (hblank : ∀ i ∈ canonicalRepairScalarSlots, R (rg i) = []) :
    metadataCleared (canonicalRepairBlockGeneratedBank R rg L n r B)
      (canonicalRepairScalarSlots.map rg) =
      canonicalHeaderScalarGeneratedBank R (rg ∘ canonicalRepairBlockHeader) L n r := by
  let header := rg ∘ canonicalRepairBlockHeader
  have empty (i : Fin 130) (hi : i ∈ canonicalRepairScalarSlots) :
      canonicalHeaderScalarGeneratedBank R header L n r (rg i) = [] := by
    rw [canonicalHeaderScalarGeneratedBank_outside R header L n r _ (by
      intro j he
      have hv := congrArg (fun k : Fin 130 => k.val) (hrg he)
      change j.val = i.val at hv
      have hj := j.isLt
      simp only [canonicalRepairScalarSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hv <;> omega)]
    exact hblank i hi
  funext k
  by_cases hk : k ∈ canonicalRepairScalarSlots.map rg
  · rw [metadataCleared_at _ _ k hk]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    exact (empty i hi).symm
  · rw [metadataCleared_keep _ _ k hk]
    have off (i : Fin 130) (hi : i ∈ canonicalRepairScalarSlots) : k ≠ rg i := by
      intro he; exact hk (he ▸ List.mem_map.mpr ⟨i,hi,rfl⟩)
    have h121 := off 121 (by simp [canonicalRepairScalarSlots])
    have h122 := off 122 (by simp [canonicalRepairScalarSlots])
    have h124 := off 124 (by simp [canonicalRepairScalarSlots])
    have h125 := off 125 (by simp [canonicalRepairScalarSlots])
    have h126 := off 126 (by simp [canonicalRepairScalarSlots])
    have h127 := off 127 (by simp [canonicalRepairScalarSlots])
    simp [canonicalRepairBlockGeneratedBank,canonicalRepairKeyGeneratedBank,
      canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,repairZeroBank,
      canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,canonicalRepairZeroCore,
      canonicalRepairZeroSlot,canonicalRepairBlockHeader,Function.comp_def,
      h121,h122,h124,h125,h126,h127]

theorem canonicalRepairScalarRestore_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n r B : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i ∈ canonicalRepairScalarSlots, S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A+4))) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (canonicalRepairScalarSlots.map rg))
        (mk v { S with R := Function.update (canonicalRepairBlockGeneratedBank S.R rg L n r B) dst output })
        (metadataCleanCost (canonicalRepairBlockGeneratedBank S.R rg L n r B)
          (canonicalRepairScalarSlots.map rg))
        (mk v' { S with R := (Function.update
          (canonicalHeaderScalarGeneratedBank S.R (rg ∘ canonicalRepairBlockHeader) L n r) dst output) }) := by
  apply metadataClean_framed_exec body _ _ _ _
    (canonicalRepairBlockGeneratedBank_restore S.R rg hrg L n r B hblank) dst _ output v S
  · exact List.Nodup.map hrg (by decide +kernel)
  · intro h
    obtain ⟨i,_,he⟩ := List.mem_map.mp h
    exact hoff i he

end
end IntegerMultBounds.MathlibTM2.Routing
