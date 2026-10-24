module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryHighPad
public import IntegerMultBounds.MathlibTM2.Routing.BinaryLowCopy

/-! Copy a binary operand into any live target width, narrower or wider.
Appending target-width zeros before extracting the low part avoids a width
comparison. The wide temporary and all traversal scratch are erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryResizeLowSlot : Fin 8 → Fin 9 := ![0,4,5,6,7,2,3,8]
theorem binaryResizeLowSlot_injective : Function.Injective binaryResizeLowSlot := by decide +kernel

def binaryResizeCopyProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 1) (rg 2) (rg 6) (rg 7))
    (.seq (binaryHighPadProgram (rg 0) (rg 4) (rg 2) (rg 5) (rg 6) (rg 7))
      (.seq (binaryPrefixExtractProgram (rg ∘ binaryResizeLowSlot)) (bclear (rg 2))))

theorem binaryResizeCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (M L W x : ℕ)
    (hW : W < 2 ^ M) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hvalue : S.R (rg 1) = binSyms L x)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 3 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * M * (4 * W + 11) + 12 * L + 26 * W + 42 ∧
      Exec body (binaryResizeCopyProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms W x ++ S.R (rg 3)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body) (a := rg 1) (c := rg 2) (t₁ := rg 6) (t₂ := rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S
    (hblank 6 (by decide) (by decide) (by decide)) (hblank 7 (by decide) (by decide) (by decide))
  rw [hvalue, hblank 2 (by decide) (by decide) (by decide), List.append_nil, length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L x) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryHighPad_exec body (rg 0) (rg 4) (rg 2) (rg 5) (rg 6) (rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) M W L x hW hx v₁ C
    (by simp [C, hrg.eq_iff, hwidth]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms (L + W) x) }
  have keep (j : Fin 9) (hj : j ≠ 2) : D.R (rg j) = S.R (rg j) := by simp [D, C, hrg.eq_iff, hj]
  have hlowBlank : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 →
      D.R ((rg ∘ binaryResizeLowSlot) j) = [] := by
    intro j hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      dsimp only [Function.comp_apply] <;> rw [keep _ (by decide)] <;> apply hblank <;> decide
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryLowCopy_exec body (rg ∘ binaryResizeLowSlot)
    (hrg.comp binaryResizeLowSlot_injective) M W L x hW v₂ D
    ((keep 0 (by decide)).trans hwidth)
    (by change D.R (rg 2) = _; simp [D, Nat.add_comm]) hlowBlank
  change Exec body _ (mk v₂ D) m₃ (mk v₃ { D with R := (Function.update D.R (rg 3)
    (binSyms W x ++ D.R (rg 3))) }) at he₃
  rw [keep 3 (by decide)] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 3) (binSyms W x ++ S.R (rg 3)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 2) v₃ E
  have hlen : (E.R (rg 2)).length = L + W := by simp [E, D, hrg.eq_iff, length_binSyms]
  have hfinal : ({ E with R := Function.update E.R (rg 2) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 3) (binSyms W x ++ S.R (rg 3)) } := by
    congr 1
    funext y
    by_cases h2 : y = rg 2
    · subst y; simp [hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    · by_cases h3 : y = rg 3 <;> simp [E, D, C, h2, h3, hrg.eq_iff]
  rw [hlen, hfinal] at he₄
  refine ⟨v₄, (6 * L + 6) + (m₂ + (m₃ + (2 * (L + W) + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩
  unfold binaryPrefixExtractCost at hm₃
  nlinarith only [hm₂, hm₃]

end IntegerMultBounds.MathlibTM2.Routing
