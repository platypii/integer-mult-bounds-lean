module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale
public import IntegerMultBounds.MathlibTM2.Routing.BinarySuccessor

/-! Generate the two shared descriptor source widths from target and borrowed
row counts. Doubling and the common sum are computed once and then erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def descriptorSourceWidthsProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (binaryDoubleCopyProgram (rg 0) (rg 2) (rg 6) (rg 7))
    (.seq (badd (rg 1) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8) (rg 9))
      (.seq (binarySuccessorProgram (rg 2) (rg 4) (rg 6) (rg 7) (rg 9))
        (.seq (binarySuccessorProgram (rg 3) (rg 5) (rg 6) (rg 7) (rg 9))
          (.seq (bclear (rg 2)) (bclear (rg 3))))))

theorem descriptorSourceWidths_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (L rows borrowed : ℕ)
    (hfit : rows + 2 * borrowed + 1 < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hborrowed : S.R (rg 0) = binSyms L borrowed) (hrows : S.R (rg 1) = binSyms L rows)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 1 → j ≠ 9 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (descriptorSourceWidthsProgram rg) (mk v S) (42 * L + 48)
        (mk v' { S with R := (Function.update (Function.update S.R (rg 4) (binSyms L (2 * borrowed + 1)))
          (rg 5) (binSyms L (rows + 2 * borrowed + 1))) }) := by
  obtain ⟨v₁, hu₁, hex₁⟩ := binaryDoubleCopy_exec body (rg 0) (rg 2) (rg 6) (rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) L borrowed v S hborrowed
    (hblank 2 (by decide) (by decide) (by decide)) (hblank 6 (by decide) (by decide) (by decide))
    (hblank 7 (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (2 * borrowed)) }
  obtain ⟨v₂, hu₂, _, _, hex₂⟩ := badd_exec (body := body)
    (a := rg 1) (b := rg 2) (c := rg 3) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : rows < 2 ^ L) (by omega : 2 * borrowed < 2 ^ L) v₁ C
    (by simp [C, hrg.eq_iff, hrows]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide)])
  have hc3 : C.R (rg 3) = [] := by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
  rw [Nat.mod_eq_of_lt (by omega : rows + 2 * borrowed < 2 ^ L), hc3, List.append_nil] at hex₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (binSyms L (rows + 2 * borrowed)) }
  obtain ⟨v₃, hu₃, hex₃⟩ := binarySuccessor_exec body (rg 2) (rg 4) (rg 6) (rg 7) (rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) L (2 * borrowed) v₂ D
    (by simp [D, C, hrg.eq_iff])
    (by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  let E : Stacks T A := { D with R := Function.update D.R (rg 4) (binSyms L (2 * borrowed + 1)) }
  obtain ⟨v₄, hu₄, hex₄⟩ := binarySuccessor_exec body (rg 3) (rg 5) (rg 6) (rg 7) (rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) L (rows + 2 * borrowed) v₃ E
    (by simp [E, D, hrg.eq_iff])
    (by simp [E, D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  let F : Stacks T A := { E with R := Function.update E.R (rg 5) (binSyms L (rows + 2 * borrowed + 1)) }
  obtain ⟨v₅, hu₅, _, hex₅⟩ := bclear_exec body (rg 2) v₄ F
  let G : Stacks T A := { F with R := Function.update F.R (rg 2) [] }
  obtain ⟨v₆, hu₆, _, hex₆⟩ := bclear_exec body (rg 3) v₅ G
  have hf2 : (F.R (rg 2)).length = L := by simp [F, E, D, C, hrg.eq_iff, length_binSyms]
  have hg3 : (G.R (rg 3)).length = L := by simp [G, F, E, D, hrg.eq_iff, length_binSyms]
  have hf : ({ G with R := Function.update G.R (rg 3) [] } : Stacks T A) =
      { S with R := (Function.update (Function.update S.R (rg 4) (binSyms L (2 * borrowed + 1)))
        (rg 5) (binSyms L (rows + 2 * borrowed + 1))) } := by
    congr 1
    funext j
    by_cases h2 : j = rg 2
    · subst j; simp [G, hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    by_cases h3 : j = rg 3
    · subst j; simp [hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
    by_cases h4 : j = rg 4
    · subst j; simp [G, F, E, D, C, hrg.eq_iff]
    by_cases h5 : j = rg 5
    · subst j; simp [G, F, E, D, C, hrg.eq_iff]
    · simp [G, F, E, D, C, h2, h3, h4, h5]
  rw [hf2] at hex₅
  rw [hg3, hf] at hex₆
  exact ⟨v₆, hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    (Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ (Exec.seq hex₅ hex₆))))).cast (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
