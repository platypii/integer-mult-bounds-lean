module

public import IntegerMultBounds.MathlibTM2.Routing.SparseAbsentCoordinateEmit

/-! Emit the zero-selector terminal coordinate from live widths. Position zero
is constructed and erased internally; no prepared terminal frame is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseTerminalCoordinateProgram (last pos wire selector gap dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bzero last pos tx)
    (.seq (sparseAbsentCoordinateProgram last pos wire selector gap dst tx ty tz cy) (bclear pos))

theorem sparseTerminalCoordinate_exec (body : P → Pr P T Q A U)
    (last pos wire selector gap dst tx ty tz cy : Fin T)
    (hregs : [last, pos, wire, selector, gap, dst, tx, ty, tz].Nodup)
    (hcyLast : cy ≠ last) (hcyPos : cy ≠ pos)
    (L Ls N : ℕ) (hN : N < 2 ^ L) (hpositive : 0 < N)
    (v : HS T Q A U) (S : Stacks T A)
    (hlast : S.R last = binSyms L (N - 1)) (hposition : S.R pos = [])
    (hwire : (S.R wire).length = Ls)
    (hselector : S.R selector = []) (hgap : S.R gap = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseTerminalCoordinateProgram last pos wire selector gap dst tx ty tz cy)
        (mk v S) (22 * L + 12 * Ls + 37)
        (mk v' { S with R := Function.update S.R dst (binSyms L (N - 1) ++ separator :: (binSyms Ls 0 ++ separator :: S.R dst)) }) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec body (wR := last) (c := pos) (t := tx)
    (by regs_nodup) v S htx
  rw [hlast, length_binSyms, hposition, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R pos (binSyms L 0) }
  obtain ⟨v₂, hu₂, he₂⟩ := sparseAbsentCoordinate_exec body last pos wire selector gap dst tx ty tz cy
    hregs hcyLast hcyPos L Ls N 0 hN hpositive v₁ S₁
    (by simp [S₁, ‹last ≠ pos›, hlast]) (by simp [S₁])
    (by simpa [S₁, Ne.symm ‹pos ≠ wire›] using hwire)
    (by simp [S₁, Ne.symm ‹pos ≠ selector›, hselector]) (by simp [S₁, Ne.symm ‹pos ≠ gap›, hgap])
    (by simp [S₁, Ne.symm ‹pos ≠ tx›, htx]) (by simp [S₁, Ne.symm ‹pos ≠ ty›, hty])
    (by simp [S₁, Ne.symm ‹pos ≠ tz›, htz])
  rw [Nat.sub_zero] at he₂
  have hd : S₁.R dst = S.R dst := by simp [S₁, Ne.symm ‹pos ≠ dst›]
  rw [hd] at he₂
  let out := binSyms L (N - 1) ++ separator :: (binSyms Ls 0 ++ separator :: S.R dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body pos v₂ S₂
  have hp : S₂.R pos = binSyms L 0 := by simp [S₂, S₁, ‹pos ≠ dst›]
  have hf : Function.update S₂.R pos [] = Function.update S.R dst out := by
    funext j
    by_cases hp : j = pos
    · subst j; simp [‹pos ≠ dst›, hposition]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hp]
      · simp [S₂, S₁, hp, hd]
  rw [hf, hp, length_binSyms] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
