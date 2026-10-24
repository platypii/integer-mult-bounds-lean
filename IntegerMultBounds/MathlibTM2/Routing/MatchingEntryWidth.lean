module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale
public import IntegerMultBounds.MathlibTM2.Routing.BinarySuccessor

/-! Derive the serialized matching-entry width `2*L+2` from binary `L`,
restoring the successor temporary and all arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingEntryWidthProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (binarySuccessorProgram (rg 0) (rg 1) (rg 3) (rg 4) (rg 5))
    (.seq (binaryDoubleCopyProgram (rg 1) (rg 2) (rg 3) (rg 4)) (bclear (rg 1)))

theorem matchingEntryWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (M L : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms M L)
    (hblank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (matchingEntryWidthProgram rg) (mk v S) (22 * M + 27)
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms M (2 * L + 2)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := binarySuccessor_exec body (rg 0) (rg 1) (rg 3) (rg 4) (rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) M L v S hsrc
    (hblank 1 (by decide) (by decide)) (hblank 3 (by decide) (by decide)) (hblank 4 (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (binSyms M (L + 1)) }
  obtain ⟨v₂, hu₂, he₂⟩ := binaryDoubleCopy_exec body (rg 1) (rg 2) (rg 3) (rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) M (L + 1) v₁ C (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 2 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 4 (by decide) (by decide)])
  rw [show 2 * (L + 1) = 2 * L + 2 by ring] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms M (2 * L + 2)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 1) v₂ D
  have hlen : (D.R (rg 1)).length = M := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 1) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms M (2 * L + 2)) } := by
    congr 1
    funext x
    by_cases hx : x = rg 1
    · subst x; simp [hrg.eq_iff, hblank 1 (by decide) (by decide)]
    · by_cases hy : x = rg 2 <;> simp [D, C, hx, hy, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
