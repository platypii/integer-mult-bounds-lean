module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySaturatingSub
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Generate both shared last-row operands from live target and borrowed row
counts. One binary constant is generated once and erased; empty rows stay zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def descriptorLastRowSlot (j : Fin 2) : Fin 7 → Fin 9 :=
  ![(if j = 0 then 0 else 1),2,(if j = 0 then 3 else 4),5,6,7,8]
theorem descriptorLastRowSlot_injective (j : Fin 2) : Function.Injective (descriptorLastRowSlot j) := by
  fin_cases j <;> decide +kernel

def descriptorLastRowsProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (bzero (rg 0) (rg 2) (rg 5))
    (.seq (countIter (rg 2) (rg 5) (rg 8))
      (.seq (binarySaturatingSubProgram (rg ∘ descriptorLastRowSlot 0))
        (.seq (binarySaturatingSubProgram (rg ∘ descriptorLastRowSlot 1)) (bclear (rg 2)))))

theorem descriptorLastRows_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L rows borrowed : ℕ)
    (hrows : rows < 2 ^ L) (hborrowed : borrowed < 2 ^ L) (hone : 1 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hrowWord : S.R (rg 0) = binSyms L rows) (hborrowedWord : S.R (rg 1) = binSyms L borrowed)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 38 * L + 41 ∧
      Exec body (descriptorLastRowsProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (rg 3) (binSyms L (rows - 1)))
          (rg 4) (binSyms L (borrowed - 1))) }) := by
  obtain ⟨v₁, hu₁, hex₁⟩ := bzero_exec (body := body) (wR := rg 0) (c := rg 2) (t := rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S (hblank 5 (by decide) (by decide) (by decide))
  rw [hrowWord, length_binSyms, hblank 2 (by decide) (by decide) (by decide), List.append_nil] at hex₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L 0) }
  obtain ⟨v₂, hu₂, hex₂⟩ := countIter_exec (body := body) (W := L) (j := 0) (c := rg 2) (tmp := rg 5) (hrg.ne (by decide))
    (rg 8) v₁ C (by simp [C]) (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
  let D : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L 1) }
  have hD : ({ C with R := Function.update C.R (rg 2) (binSyms L (0 + 1)) } : Stacks T A) = D := by simp [C, D]
  rw [hD] at hex₂
  have hdKeep (j : Fin 9) (hj : j ≠ 2) : D.R (rg j) = S.R (rg j) := by simp [D, hrg.eq_iff, hj]
  have hdBlank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 →
      D.R ((rg ∘ descriptorLastRowSlot 0) j) = [] := by
    intro j h0 h1 h6
    fin_cases j <;> simp_all [descriptorLastRowSlot, D, hrg.eq_iff]
  obtain ⟨v₃, m₃, hu₃, hm₃, hex₃⟩ := binarySaturatingSub_exec body (rg ∘ descriptorLastRowSlot 0)
    (hrg.comp (descriptorLastRowSlot_injective 0)) L rows 1 hrows hone v₂ D
    ((hdKeep 0 (by decide)).trans hrowWord) (by change D.R (rg 2) = _; simp [D]) hdBlank
  let E : Stacks T A := { D with R := Function.update D.R (rg 3) (binSyms L (rows - 1)) }
  have heKeep (j : Fin 9) (hj : j ≠ 3) : E.R (rg j) = D.R (rg j) := by simp [E, hrg.eq_iff, hj]
  have heBlank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 →
      E.R ((rg ∘ descriptorLastRowSlot 1) j) = [] := by
    intro j h0 h1 h6
    fin_cases j <;> simp_all [descriptorLastRowSlot, E, D, hrg.eq_iff]
  obtain ⟨v₄, m₄, hu₄, hm₄, hex₄⟩ := binarySaturatingSub_exec body (rg ∘ descriptorLastRowSlot 1)
    (hrg.comp (descriptorLastRowSlot_injective 1)) L borrowed 1 hborrowed hone v₃ E
    ((heKeep 1 (by decide)).trans ((hdKeep 1 (by decide)).trans hborrowedWord))
    (by change E.R (rg 2) = _; simp [E, D, hrg.eq_iff]) heBlank
  let F : Stacks T A := { E with R := Function.update E.R (rg 4) (binSyms L (borrowed - 1)) }
  obtain ⟨v₅, hu₅, _, hex₅⟩ := bclear_exec body (rg 2) v₄ F
  have hlen : (F.R (rg 2)).length = L := by simp [F, E, D, hrg.eq_iff, length_binSyms]
  have hf : ({ F with R := Function.update F.R (rg 2) [] } : Stacks T A) =
      { S with R := (Function.update (Function.update S.R (rg 3) (binSyms L (rows - 1)))
        (rg 4) (binSyms L (borrowed - 1))) } := by
    congr 1
    funext j
    by_cases h2 : j = rg 2
    · subst j; simp [hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    by_cases h3 : j = rg 3
    · subst j; simp [F, E, D, hrg.eq_iff]
    by_cases h4 : j = rg 4
    · subst j; simp [F, E, D, hrg.eq_iff]
    · simp [F, E, D, h2, h3, h4]
  rw [hlen, hf] at hex₅
  exact ⟨v₅, (4 * L + 4) + ((4 * L + 5) + (m₃ + (m₄ + (2 * L + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega,
    Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ hex₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
