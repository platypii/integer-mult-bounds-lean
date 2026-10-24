module

public import IntegerMultBounds.MathlibTM2.Routing.RouterAuxiliaryGenerate
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Restore auxiliary count, target-width and one-row operands after a caller
has serialized them. The original three binary sources are retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

theorem routerAuxiliaryBank_restore (R : Fin T → List (Fin (A+4)))
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ)
    (hblank : ∀ i : Fin 12, i = 3 ∨ i = 4 ∨ i = 5 → R (rg i) = []) :
    metadataCleared (routerAuxiliaryBank R rg W n wy) [rg 3,rg 4,rg 5] = R := by
  funext k
  by_cases h3 : k = rg 3
  · subst k; simp [metadataCleared,hblank 3 (by simp)]
  by_cases h4 : k = rg 4
  · subst k; simp [metadataCleared,hrg.eq_iff,hblank 4 (by simp)]
  by_cases h5 : k = rg 5
  · subst k; simp [metadataCleared,hrg.eq_iff,hblank 5 (by simp)]
  simp [metadataCleared,routerAuxiliaryBank,h3,h4,h5]

theorem routerAuxiliaryCleanCost (R : Fin T → List (Fin (A+4)))
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ) :
    metadataCleanCost (routerAuxiliaryBank R rg W n wy) [rg 3,rg 4,rg 5] =
      2*W+2*canonicalScalarWidth wy+9 := by
  simp [metadataCleanCost,routerAuxiliaryBank,hrg.eq_iff,length_binSyms]
  omega

theorem routerAuxiliaryClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i : Fin 12, i = 3 ∨ i = 4 ∨ i = 5 → S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A+4))) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean [rg 3,rg 4,rg 5])
        (mk v { S with R := Function.update (routerAuxiliaryBank S.R rg W n wy) dst output })
        (2*W+2*canonicalScalarWidth wy+9)
        (mk v' { S with R := Function.update S.R dst output }) := by
  obtain ⟨v',hu,he⟩ := metadataClean_framed_exec body [rg 3,rg 4,rg 5]
    (by simp [List.nodup_cons,hrg.eq_iff]) (routerAuxiliaryBank S.R rg W n wy) S.R
    (routerAuxiliaryBank_restore S.R rg hrg W n wy hblank) dst
    (by simp [(hoff 3).symm,(hoff 4).symm,(hoff 5).symm]) output v S
  rw [routerAuxiliaryCleanCost S.R rg hrg W n wy] at he
  exact ⟨v',hu,he⟩

end IntegerMultBounds.MathlibTM2.Routing
