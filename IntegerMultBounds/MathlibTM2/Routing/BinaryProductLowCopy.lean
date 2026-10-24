module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryLowCopy
public import IntegerMultBounds.MathlibTM2.Host.BinArithMul

/-! Multiply two binary operands and export their fixed-width low product. The wide multiplication result is erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryProductLowSlot : Fin 8 → Fin 11 := ![2,3,4,5,6,7,8,9]
theorem binaryProductLowSlot_injective : Function.Injective binaryProductLowSlot := by decide +kernel

def binaryProductLowCopyProgram (rg : Fin 11 → Fin T) : Pr P T Q A U :=
  .seq (bmul (rg 0) (rg 1) (rg 7) (rg 3) (rg 4) (rg 5) (rg 6) (rg 9) (rg 10))
    (.seq (binaryPrefixExtractProgram (rg ∘ binaryProductLowSlot)) (bclear (rg 7)))

theorem binaryProductLowCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (M L x y : ℕ)
    (hL : L < 2 ^ M) (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hleft : S.R (rg 0) = binSyms L (x)) (hright : S.R (rg 1) = binSyms L y)
    (hwidth : S.R (rg 2) = binSyms M L)
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (24 * L + 20) + 50 * L + 44 + M * (4 * L + 11) ∧
      Exec body (binaryProductLowCopyProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 8) (binSyms L ((x * y))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := bmul_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 7) (s := rg 3) (t := rg 4) (tx := rg 5) (ty := rg 6) (tz := rg 9) (cy := rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hx hy v S
    hleft hright (hblank 7 (by decide) (by decide) (by decide) (by decide))
    (hblank 3 (by decide) (by decide) (by decide) (by decide))
    (hblank 4 (by decide) (by decide) (by decide) (by decide))
    (hblank 5 (by decide) (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide) (by decide))
    (hblank 9 (by decide) (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 7) (binSyms (L + L) ((x * y))) }
  have keep (j : Fin 11) (hj : j ≠ 7) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  have hlowBlank : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → C.R ((rg ∘ binaryProductLowSlot) j) = [] := by
    intro j hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      dsimp only [Function.comp_apply] <;> rw [keep _ (by decide)] <;> apply hblank <;> decide
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryLowCopy_exec body (rg ∘ binaryProductLowSlot)
    (hrg.comp binaryProductLowSlot_injective) M L L ((x * y)) hL v₁ C
    ((keep 2 (by decide)).trans hwidth) (by change C.R (rg 7) = _; simp [C]) hlowBlank
  have hc8 : C.R (rg 8) = [] := (keep 8 (by decide)).trans
    (hblank 8 (by decide) (by decide) (by decide) (by decide))
  change Exec body _ (mk v₁ C) m₂ (mk v₂ { C with R := (Function.update C.R (rg 8)
    (binSyms L ((x * y)) ++ C.R (rg 8))) }) at he₂
  rw [hc8, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 8) (binSyms L ((x * y))) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 7) v₂ D
  have hlen : (D.R (rg 7)).length = L + L := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 7) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 8) (binSyms L ((x * y))) } := by
    congr 1
    funext x
    by_cases h7 : x = rg 7
    · subst x; simp [hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h8 : x = rg 8 <;> simp [D, C, h7, h8, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * (L + L) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  unfold binaryPrefixExtractCost at hm₂
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Routing
