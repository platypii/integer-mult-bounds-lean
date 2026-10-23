module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryInactiveProfileFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryWordRepeat

/-! Build an arbitrary inactive profile from binary count and width operands.
The frame template is generated and erased; every non-output tape is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def inactiveProfileZeroReg (rg : Fin 9 → Fin T) : BinaryZeroReg → Fin T
  | .width => rg 0
  | .unary => rg 4
  | .dst => rg 2
  | .scratch i => rg ⟨6 + i.val, by omega⟩

theorem inactiveProfileZeroReg_injective (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) :
    Function.Injective (inactiveProfileZeroReg rg) := by
  intro r s h
  cases r <;> cases s <;>
    have hv := congrArg Fin.val (hrg h) <;>
    (try dsimp only at hv) <;>
    first | rfl | omega | (apply congrArg BinaryZeroReg.scratch; apply Fin.ext; omega)

def binaryInactiveProfileProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryInactiveProfileFrameProgram (inactiveProfileZeroReg rg))
    (.seq (binaryWordRepeatProgram (rg 1) (rg 4) (rg 5) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8))
      (bclear (rg 2)))

def binaryInactiveProfileCost (Lw Lc L n : ℕ) : ℕ :=
  (Lw * (4 * L + 11) + 8 * L + 15) + binaryWordRepeatCost Lc n (L + 3) + (2 * (L + 3) + 2)

theorem wordCopies_inactiveProfile (L n : ℕ) :
    wordCopies (affineProfileFrames (A := A) L [(false, 0)]) n =
      affineProfileFrames L (List.replicate n (false, 0)) := by
  have hcomm (word : List (Fin (A + 4))) (n : ℕ) :
      wordCopies word n ++ word = word ++ wordCopies word n := by
    induction n with
    | zero => simp [wordCopies]
    | succ n ih => simp only [wordCopies, List.append_assoc, ih]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordCopies, hcomm, ih]
    simp [affineProfileFrames, List.replicate_succ, List.append_assoc]

theorem binaryInactiveProfile_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg)
    (Lw Lc L n : ℕ) (hL : L < 2 ^ Lw) (hn : n < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms Lw L) (hcount : S.R (rg 1) = binSyms Lc n)
    (hblank : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 3 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryInactiveProfileCost Lw Lc L n ∧
      Exec body (binaryInactiveProfileProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 3) (affineProfileFrames L (List.replicate n (false, 0)) ++ S.R (rg 3)) }) := by
  have hblank₂ := hblank 2 (by decide) (by decide) (by decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binaryInactiveProfileFrame_exec body (inactiveProfileZeroReg rg)
    (inactiveProfileZeroReg_injective rg hrg) Lw L hL v S hwidth
    (hblank 4 (by decide) (by decide) (by decide))
    (by
      intro i
      apply hblank ⟨6 + i.val, by omega⟩
      · intro h; have hv := congrArg Fin.val h; change 6 + i.val = 0 at hv; omega
      · intro h; have hv := congrArg Fin.val h; change 6 + i.val = 1 at hv; omega
      · intro h; have hv := congrArg Fin.val h; change 6 + i.val = 3 at hv; omega)
  let word := affineProfileFrames (A := A) L [(false, 0)]
  have hword : word.length = L + 3 := by simp [word, affineProfileFrames]; omega
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg 2) word }
  have he₁ : Exec body (binaryInactiveProfileFrameProgram (inactiveProfileZeroReg rg)) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [inactiveProfileZeroReg, hblank₂, List.append_nil] using hx₁
  have hkeep (i : Fin 9) (hi : i ≠ 2) : S₁.R (rg i) = S.R (rg i) := by
    simp [S₁, hrg.eq_iff, hi]
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := binaryWordRepeat_exec body
    (rg 1) (rg 4) (rg 5) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) Lc n hn word v₁ S₁
    ((hkeep 1 (by decide)).trans hcount) (by simp [S₁])
    ((hkeep 4 (by decide)).trans (hblank 4 (by decide) (by decide) (by decide)))
    ((hkeep 5 (by decide)).trans (hblank 5 (by decide) (by decide) (by decide)))
    ((hkeep 6 (by decide)).trans (hblank 6 (by decide) (by decide) (by decide)))
    ((hkeep 7 (by decide)).trans (hblank 7 (by decide) (by decide) (by decide)))
    ((hkeep 8 (by decide)).trans (hblank 8 (by decide) (by decide) (by decide)))
  rw [hword] at hm₂
  let out := affineProfileFrames (A := A) L (List.replicate n (false, 0)) ++ S.R (rg 3)
  have he₂ : Exec body (binaryWordRepeatProgram (rg 1) (rg 4) (rg 5) (rg 2) (rg 3) (rg 6) (rg 7) (rg 8))
      (mk v₁ S₁) m₂ (mk v₂ { S₁ with R := Function.update S₁.R (rg 3) out }) := by
    simpa only [word, wordCopies_inactiveProfile, hkeep 3 (by decide)] using hx₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg 3) out }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 2) v₂ S₂
  have htemplate : S₂.R (rg 2) = word := by simp [S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₂.R (rg 2) [] = Function.update S.R (rg 3) out := by
    funext j
    by_cases hj : j = rg 2
    · subst j; simp [hrg.eq_iff, hblank₂]
    · simp [S₂, S₁, Function.update_apply, hj]
  rw [htemplate, hword, hf] at hx₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (L + 3) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryInactiveProfileCost; omega, Exec.seq he₁ (Exec.seq he₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
