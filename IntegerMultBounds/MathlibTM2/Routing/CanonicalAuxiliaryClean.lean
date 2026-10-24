module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalAuxiliaryGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RouterAuxiliaryClean

/-! Restore the common canonical setup and all three auxiliary outputs.
Only fifteen generated words are erased; original inputs and spectators survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalAuxiliaryTargets : List (Fin 49) := [1,2,11,14,16,17,19,21,25,26,27,44,46,47,48]

theorem canonicalAuxiliaryBank_keep (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (L n r : ℕ) (k : Fin T) (hk : k ∉ canonicalAuxiliaryTargets.map rg) :
    canonicalAuxiliaryBank R rg L n r k = R k := by
  have off (i : Fin 49) (hi : i ∈ canonicalAuxiliaryTargets) : k ≠ rg i := by
    intro h; exact hk (h ▸ List.mem_map.mpr ⟨i,hi,rfl⟩)
  simp only [canonicalAuxiliaryBank,routerAuxiliaryBank,canonicalDescriptorScalarInputBank,
    canonicalProfileSetupBank,canonicalDescriptorWidthsBank,canonicalResidueGeometryBank,
    canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,Function.comp_apply]
  repeat rw [Function.update_of_ne (off _ (by decide +kernel))]

theorem canonicalAuxiliaryBank_restore (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (L n r : ℕ)
    (hblank : ∀ i ∈ canonicalAuxiliaryTargets, R (rg i) = []) :
    metadataCleared (canonicalAuxiliaryBank R rg L n r) (canonicalAuxiliaryTargets.map rg) = R := by
  funext k
  by_cases hk : k ∈ canonicalAuxiliaryTargets.map rg
  · rw [metadataCleared_at _ _ _ hk]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    exact (hblank i hi).symm
  · rw [metadataCleared_keep _ _ _ hk,canonicalAuxiliaryBank_keep R rg L n r k hk]

theorem canonicalAuxiliaryCleanCost (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    metadataCleanCost (canonicalAuxiliaryBank R rg L n r) (canonicalAuxiliaryTargets.map rg) =
      24*L+2*(canonicalStageWidths p).indexBits+2*canonicalScalarWidth p.wy+33 := by
  simp [metadataCleanCost,canonicalAuxiliaryTargets,canonicalAuxiliaryBank,routerAuxiliaryBank,
    canonicalDescriptorScalarInputBank,canonicalProfileSetupBank,canonicalDescriptorWidthsBank,
    canonicalResidueGeometryBank,canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
    canonicalAuxiliaryCore,canonicalAuxiliarySlot,canonicalDescriptorGeometrySlot,canonicalProfileWidthSlot,
    canonicalProfileGeometrySlot,canonicalResidueCommonSlot,routerReservoirCommonSlot,
    Function.comp_def,hrg.eq_iff,length_binSyms]
  omega

theorem canonicalAuxiliaryClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i ∈ canonicalAuxiliaryTargets, S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A+4))) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (canonicalAuxiliaryTargets.map rg))
        (mk v { S with R := Function.update (canonicalAuxiliaryBank S.R rg L n r) dst output })
        (24*L+2*(canonicalStageWidths p).indexBits+2*canonicalScalarWidth p.wy+33)
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  obtain ⟨v',hu,he⟩ := metadataClean_framed_exec body (canonicalAuxiliaryTargets.map rg)
    (List.Nodup.map hrg (by decide +kernel)) (canonicalAuxiliaryBank S.R rg L n r) S.R
    (canonicalAuxiliaryBank_restore S.R rg L n r hblank) dst
    (by intro h; obtain ⟨i,_,he⟩ := List.mem_map.mp h; exact hoff i he) output v S
  rw [canonicalAuxiliaryCleanCost S.R rg hrg L n r] at he
  exact ⟨v',hu,he⟩

end IntegerMultBounds.MathlibTM2.Routing
