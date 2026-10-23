module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryEmit

/-! Load a matching entry, derive its coordinate/activity frame, and accumulate it
in. The complete entry is archived and the live endpoint bank is erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def residueEntryStepProgram (rg : Fin 18 → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg 14) (rg 15) (rg 0) (rg 12) (rg 16))
    (.seq (residueEntryEmitProgram (fun j => rg (j.castAdd 4)))
      (.seq (bclear (rg 0)) (.seq (bclear (rg 12)) (moveR (rg 13) (rg 17) id))))

def residueEntryStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L _Lk q mate k r : ℕ) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R (rg 14) rest)
    (rg 15) ((matchingEntryWord L q mate).reverse ++ R (rg 15))) (rg 17)
    ((residueEntryWord L q mate k r).reverse ++ R (rg 17))

theorem residueEntryStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg)
    (L Lk q mate k r : ℕ) (hq : q < 2 ^ L) (hk : k < 2 ^ Lk) (hk0 : 0 < k) (hr : r < 2 ^ Lk)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 14) = matchingEntryWord L q mate ++ rest)
    (hblank : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (rg j) = [])
    (hstride : S.R (rg 1) = binSyms Lk k) (hresidue : S.R (rg 11) = binSyms Lk r)
    (htmp : S.R (rg 16) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps + 2 ≤ residueDispatchCost L Lk + 28 * L + 47 ∧
      Exec body (residueEntryStepProgram rg) (mk v S) steps
        (mk v' { S with R := residueEntryStepBank S.R rg L Lk q mate k r rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg 14) (rg 15) (rg 0) (rg 12) (rg 16)
    (by simp [List.nodup_cons, hrg.eq_iff]) L L q mate rest v S
    (by simpa [matchingEntryWord, List.append_assoc] using hinput)
    (hblank 0 (by decide)) (hblank 12 (by decide)) htmp
  let B := selectorRunLoaded S.R (rg 14) (rg 15) (rg 0) (rg 12) (binSyms L q) (binSyms L mate) rest
  let G : Stacks T A := { S with R := B }
  have hkeep (j : Fin 18) (h0 : j ≠ 0) (h1 : j ≠ 12) (h7 : j ≠ 14) (h8 : j ≠ 15) : G.R (rg j) = S.R (rg j) := by
    simp [G, B, selectorRunLoaded, hrg.eq_iff, h0, h1, h7, h8]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := residueEntryEmit_exec body (fun j => rg (j.castAdd 4))
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 18 => x.val) (hrg h))) L Lk q mate k r hq hk hk0 hr v₁ G
    (by simp [G, B, selectorRunLoaded, hrg.eq_iff])
    (by simp [G, B, selectorRunLoaded])
    ((hkeep 1 (by decide) (by decide) (by decide) (by decide)).trans hstride)
    ((hkeep 11 (by decide) (by decide) (by decide) (by decide)).trans hresidue)
    (by intro j hj hk
        rw [hkeep (j.castAdd 4)
          (by intro he; have hv : j.val = 0 := congrArg (fun x : Fin 18 => x.val) he; omega)
          (by intro he; have hv : j.val = 12 := congrArg (fun x : Fin 18 => x.val) he; omega)
          (by intro he; have hv : j.val = 14 := congrArg (fun x : Fin 18 => x.val) he; omega)
          (by intro he; have hv : j.val = 15 := congrArg (fun x : Fin 18 => x.val) he; omega)]
        exact hblank (j.castAdd 4) (Or.inr (Or.inr (Or.inr ⟨hj, hk⟩))))
  let word := residueEntryWord (A := A) L q mate k r
  have h6 : G.R (rg 13) = [] := (hkeep 13 (by decide) (by decide) (by decide) (by decide)).trans (hblank 13 (by decide))
  simp only [show Fin.castAdd 4 (13 : Fin 14) = (13 : Fin 18) from rfl, h6, List.append_nil] at he₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 13) word }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg 0) v₂ H
  let J : Stacks T A := { H with R := Function.update H.R (rg 0) [] }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec body (rg 12) v₃ J
  let E : Stacks T A := { J with R := Function.update J.R (rg 12) [] }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body (rg 13) (rg 17) (hrg.ne (by decide)) id v₄ E
  have h0 : (H.R (rg 0)).length = L := by simp [H, G, B, selectorRunLoaded, hrg.eq_iff]
  have h1 : (J.R (rg 12)).length = L := by simp [J, H, G, B, selectorRunLoaded, hrg.eq_iff]
  have hw : E.R (rg 13) = word := by simp [E, J, H, hrg.eq_iff]
  have hf : movedR E.R (rg 13) (rg 17) id (E.R (rg 13)) = residueEntryStepBank S.R rg L Lk q mate k r rest := by
    rw [hw]
    funext j
    by_cases h7 : j = rg 14
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, word, hrg.eq_iff]
    by_cases h8 : j = rg 15
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, matchingEntryWord, word, hrg.eq_iff]
    by_cases h0 : j = rg 0
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, word, hrg.eq_iff, hblank 0 (by decide)]
    by_cases h1 : j = rg 12
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, word, hrg.eq_iff, hblank 12 (by decide)]
    by_cases h6 : j = rg 13
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, word, hrg.eq_iff, hblank 13 (by decide)]
    by_cases h10 : j = rg 17
    · subst j; simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, word, hrg.eq_iff]
    · simp [movedR, E, J, H, G, B, selectorRunLoaded, residueEntryStepBank, h7, h8, h0, h1, h6, h10]
  rw [h0] at he₃
  rw [h1] at he₄
  rw [hf, hw] at he₅
  have hword : word.length ≤ 2 * L + 2 := residueEntryWord_length_le L q mate k r
  exact ⟨v₅, (4 * L + 4 * L + 12) + (m₂ + ((2 * L + 2) +
      ((2 * L + 2) + (2 * word.length + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
