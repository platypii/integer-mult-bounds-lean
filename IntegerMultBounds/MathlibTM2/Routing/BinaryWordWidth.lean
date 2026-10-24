module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Count a preserved word's symbols into a binary word of the same width.
The width reference is copied, used and erased inside the program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryWordWidthProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) (rg 1) (rg 3) (rg 4))
    (.seq (toBinary (rg 0) (rg 1) (rg 2) (rg 3) (rg 4) (rg 5)) (bclear (rg 1)))

theorem binaryWordWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hlen : (S.R (rg 0)).length = L)
    (hblank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 22 * L + 16 ∧
      Exec body (binaryWordWidthProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L L) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body)
    (a := rg 0) (c := rg 1) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S (hblank 3 (by decide) (by decide)) (hblank 4 (by decide) (by decide))
  rw [hblank 1 (by decide) (by decide), List.append_nil, hlen] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (S.R (rg 0)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toBinary_exec (body := body)
    (u := rg 0) (wR := rg 1) (c := rg 2) (t := rg 3) (tmp := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) (rg 5) v₁ C
    (by simp [C, hrg.eq_iff, hblank 2 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 4 (by decide) (by decide)])
  have hc0 : (C.R (rg 0)).length = L := by simp [C, hrg.eq_iff, hlen]
  have hc1 : (C.R (rg 1)).length = L := by simp [C, hlen]
  rw [hc0, hc1] at he₂ hm₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms L L) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 1) v₂ D
  have hd1 : (D.R (rg 1)).length = L := by simp [D, C, hrg.eq_iff, hlen]
  have hfinal : ({ D with R := Function.update D.R (rg 1) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L L) } := by
    congr 1
    funext x
    by_cases hx : x = rg 1
    · subst x; simp [hrg.eq_iff, hblank 1 (by decide) (by decide)]
    · by_cases hy : x = rg 2 <;> simp [D, C, hx, hy, hrg.eq_iff]
  rw [hd1, hfinal] at he₃
  refine ⟨v₃, (6 * L + 6) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [hm₂]

end IntegerMultBounds.MathlibTM2.Routing
