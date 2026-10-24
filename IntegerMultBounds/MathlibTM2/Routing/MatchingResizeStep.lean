module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingEntryResize

/-! One table-width conversion step archives the original entry, emits the
resized entry into a reverse accumulator, and erases loaded endpoints. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingResizeEntrySlot : Fin 10 → Fin 14 := Fin.castLE (by decide)
theorem matchingResizeEntrySlot_injective : Function.Injective matchingResizeEntrySlot := by decide +kernel

def matchingResizeStepProgram (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg 10) (rg 11) (rg 1) (rg 2) (rg 12))
    (.seq (matchingEntryResizeProgram (rg ∘ matchingResizeEntrySlot))
      (.seq (bclear (rg 1)) (.seq (bclear (rg 2)) (moveR (rg 3) (rg 13) id))))

def matchingResizeStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 14 → Fin T)
    (L W q mate : ℕ) (rest : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R (rg 10) rest)
    (rg 11) ((matchingEntryWord L q mate).reverse ++ R (rg 11)))
    (rg 13) ((matchingEntryWord W q mate).reverse ++ R (rg 13))

theorem matchingResizeStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (M L W q mate : ℕ)
    (hW : W < 2 ^ M) (hq : q < 2 ^ L) (hmate : mate < 2 ^ L)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W)
    (hinput : S.R (rg 10) = matchingEntryWord L q mate ++ rest)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 10 → j ≠ 11 → j ≠ 13 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * M * (4 * W + 11) + 36 * L + 56 * W + 108 ∧
      Exec body (matchingResizeStepProgram rg) (mk v S) m
        (mk v' { S with R := matchingResizeStepBank S.R rg L W q mate rest }) := by
  obtain ⟨v₁, hu₁, hex₁⟩ := selectorRunLoad_exec body (rg 10) (rg 11) (rg 1) (rg 2) (rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) L L q mate rest v S
    (by simpa [matchingEntryWord, List.append_assoc] using hinput)
    (hblank 1 (by decide) (by decide) (by decide) (by decide))
    (hblank 2 (by decide) (by decide) (by decide) (by decide))
    (hblank 12 (by decide) (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := (selectorRunLoaded S.R (rg 10) (rg 11) (rg 1) (rg 2)
    (binSyms L q) (binSyms L mate) rest) }
  have keep (j : Fin 14) (h1 : j ≠ 1) (h2 : j ≠ 2) (h10 : j ≠ 10) (h11 : j ≠ 11) :
      C.R (rg j) = S.R (rg j) := by simp [C, selectorRunLoaded, hrg.eq_iff, h1, h2, h10, h11]
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := matchingEntryResize_exec body (rg ∘ matchingResizeEntrySlot)
    (hrg.comp matchingResizeEntrySlot_injective) M L W q mate hW hq hmate v₁ C
    ((keep 0 (by decide) (by decide) (by decide) (by decide)).trans hwidth)
    (by simp [C, selectorRunLoaded, matchingResizeEntrySlot, hrg.eq_iff])
    (by simp [C, selectorRunLoaded, matchingResizeEntrySlot])
    (by intro j h0 h1 h2 h3
        have hj10 : matchingResizeEntrySlot j ≠ 10 := by have := j.isLt; intro h; have := congrArg Fin.val h; simp [matchingResizeEntrySlot] at this; omega
        have hj11 : matchingResizeEntrySlot j ≠ 11 := by have := j.isLt; intro h; have := congrArg Fin.val h; simp [matchingResizeEntrySlot] at this; omega
        have hj1 : matchingResizeEntrySlot j ≠ 1 := fun h => h1 (Fin.ext (congrArg (fun k : Fin 14 => k.val) h))
        have hj2 : matchingResizeEntrySlot j ≠ 2 := fun h => h2 (Fin.ext (congrArg (fun k : Fin 14 => k.val) h))
        rw [show (rg ∘ matchingResizeEntrySlot) j = rg (matchingResizeEntrySlot j) from rfl,
          keep _ hj1 hj2 hj10 hj11]
        apply hblank
        · exact fun h => h0 (Fin.ext (congrArg (fun k : Fin 14 => k.val) h))
        · exact hj10
        · exact hj11
        · intro h; have := j.isLt; have := congrArg (fun k : Fin 14 => k.val) h; simp [matchingResizeEntrySlot] at this; omega)
  have hc3 : C.R (rg 3) = [] := (keep 3 (by decide) (by decide) (by decide) (by decide)).trans
    (hblank 3 (by decide) (by decide) (by decide) (by decide))
  change Exec body _ (mk v₁ C) m₂ (mk v₂ { C with R := (Function.update C.R (rg 3)
    (matchingEntryWord W q mate ++ C.R (rg 3))) }) at hex₂
  rw [hc3, List.append_nil] at hex₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (matchingEntryWord W q mate) }
  obtain ⟨v₃, hu₃, _, hex₃⟩ := bclear_exec body (rg 1) v₂ D
  let E : Stacks T A := { D with R := Function.update D.R (rg 1) [] }
  obtain ⟨v₄, hu₄, _, hex₄⟩ := bclear_exec body (rg 2) v₃ E
  let F : Stacks T A := { E with R := Function.update E.R (rg 2) [] }
  obtain ⟨v₅, hu₅, hex₅⟩ := moveR_exec body (rg 3) (rg 13) (hrg.ne (by decide)) id v₄ F
  have hlen1 : (D.R (rg 1)).length = L := by simp [D, C, selectorRunLoaded, hrg.eq_iff]
  have hlen2 : (E.R (rg 2)).length = L := by simp [E, D, C, selectorRunLoaded, hrg.eq_iff]
  have hf3 : F.R (rg 3) = matchingEntryWord W q mate := by simp [F, E, D, hrg.eq_iff]
  have hfinal : movedR F.R (rg 3) (rg 13) id (F.R (rg 3)) = matchingResizeStepBank S.R rg L W q mate rest := by
    rw [hf3]
    funext j
    by_cases h1 : j = rg 1
    · subst j; simp [movedR, F, E, D, C, selectorRunLoaded, matchingResizeStepBank, hrg.eq_iff, hblank 1 (by decide) (by decide) (by decide) (by decide)]
    by_cases h2 : j = rg 2
    · subst j; simp [movedR, F, E, D, C, selectorRunLoaded, matchingResizeStepBank, hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide) (by decide)]
    by_cases h3 : j = rg 3
    · subst j; simp [movedR, F, E, D, C, selectorRunLoaded, matchingResizeStepBank, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h13 : j = rg 13 <;> by_cases h10 : j = rg 10 <;> by_cases h11 : j = rg 11 <;>
        simp [movedR, F, E, D, C, selectorRunLoaded, matchingResizeStepBank,
          matchingEntryWord, h1, h2, h3, h13, h10, h11, hrg.eq_iff]

  rw [hlen1] at hex₃
  rw [hlen2] at hex₄
  rw [hfinal, hf3] at hex₅
  have hlen : (matchingEntryWord (A := A) W q mate).length = 2 * W + 2 := by simp [matchingEntryWord, length_binSyms]; omega
  rw [hlen] at hex₅
  exact ⟨v₅, (4 * L + 4 * L + 12) + (m₂ + ((2 * L + 2) + ((2 * L + 2) + (2 * (2 * W + 2) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega,
    Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ hex₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
