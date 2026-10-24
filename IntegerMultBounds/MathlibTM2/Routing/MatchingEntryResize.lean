module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeCopy
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateStep

/-! Re-encode loaded matching endpoints at a live target width. Sources and
arithmetic scratch restore; the resized delimited entry is prepended to output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryResizeDelimitedProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt (rg 3)) (fun _ => separator) .done)) (binaryResizeCopyProgram rg)

theorem binaryResizeDelimited_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (M L W x : ℕ)
    (hW : W < 2 ^ M) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hvalue : S.R (rg 1) = binSyms L x)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 3 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * M * (4 * W + 11) + 12 * L + 26 * W + 43 ∧
      Exec body (binaryResizeDelimitedProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms W x ++ separator :: S.R (rg 3)) }) := by
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (separator :: S.R (rg 3)) }
  have hp : (Action.push (.rt (rg 3)) (fun _ => separator) .done : Act T Q A U).run (mk v S) = mk v C := by
    simp [Action.run, update_rt, C]
  obtain ⟨v', m, hu, hm, hex⟩ := binaryResizeCopy_exec body rg hrg M L W x hW hx v C
    (by simp [C, hrg.eq_iff, hwidth]) (by simp [C, hrg.eq_iff, hvalue])
    (by intro j h0 h1 h3; simpa [C, hrg.eq_iff, h3] using hblank j h0 h1 h3)
  have hf : ({ C with R := Function.update C.R (rg 3) (binSyms W x ++ C.R (rg 3)) } : Stacks T A) =
      { S with R := Function.update S.R (rg 3) (binSyms W x ++ separator :: S.R (rg 3)) } := by
    simp [C]
  rw [hf] at hex
  exact ⟨v', 1 + m, hu, by omega, Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) hex⟩

def matchingEntryResizeSlot (mate : Bool) : Fin 9 → Fin 10 :=
  ![0, (if mate then 2 else 1), 4, 3, 5, 6, 7, 8, 9]
theorem matchingEntryResizeSlot_injective (mate : Bool) : Function.Injective (matchingEntryResizeSlot mate) := by
  cases mate <;> decide +kernel

def matchingEntryResizeProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (binaryResizeDelimitedProgram (rg ∘ matchingEntryResizeSlot true))
    (binaryResizeDelimitedProgram (rg ∘ matchingEntryResizeSlot false))

theorem matchingEntryResize_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (M L W q mate : ℕ)
    (hW : W < 2 ^ M) (hq : q < 2 ^ L) (hmate : mate < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hcoordinate : S.R (rg 1) = binSyms L q)
    (hmateWord : S.R (rg 2) = binSyms L mate)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * M * (4 * W + 11) + 24 * L + 52 * W + 86 ∧
      Exec body (matchingEntryResizeProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 3) (matchingEntryWord W q mate ++ S.R (rg 3)) }) := by
  have hb (b : Bool) (j : Fin 9) (h0 : j ≠ 0) (h1 : j ≠ 1) (h3 : j ≠ 3) :
      S.R ((rg ∘ matchingEntryResizeSlot b) j) = [] := by
    cases b <;> fin_cases j <;> simp_all [matchingEntryResizeSlot]
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := binaryResizeDelimited_exec body (rg ∘ matchingEntryResizeSlot true)
    (hrg.comp (matchingEntryResizeSlot_injective true)) M L W mate hW hmate v S hwidth hmateWord (hb true)
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms W mate ++ separator :: S.R (rg 3)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := binaryResizeDelimited_exec body (rg ∘ matchingEntryResizeSlot false)
    (hrg.comp (matchingEntryResizeSlot_injective false)) M L W q hW hq v₁ C
    (by simp [C, matchingEntryResizeSlot, hrg.eq_iff, hwidth])
    (by simp [C, matchingEntryResizeSlot, hrg.eq_iff, hcoordinate])
    (by intro j h0 h1 h3
        have hne : matchingEntryResizeSlot false j ≠ 3 := by fin_cases j <;> simp_all [matchingEntryResizeSlot]
        simpa [C, hrg.eq_iff, hne] using hb false j h0 h1 h3)
  have hf : ({ C with R := Function.update C.R (rg 3) (binSyms W q ++ separator :: C.R (rg 3)) } : Stacks T A) =
      { S with R := Function.update S.R (rg 3) (matchingEntryWord W q mate ++ S.R (rg 3)) } := by
    simp [C, matchingEntryWord, List.append_assoc]
  change Exec body _ (mk v₁ C) m₂ (mk v₂ { C with R := (Function.update C.R (rg 3)
    (binSyms W q ++ separator :: C.R (rg 3))) }) at hex₂
  rw [hf] at hex₂
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by nlinarith only [hm₁, hm₂], Exec.seq hex₁ hex₂⟩

end IntegerMultBounds.MathlibTM2.Routing
