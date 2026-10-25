module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Convert positive real setup words to the host binary format -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem realWord_bits (hA : 4 ≤ A) (W x : ℕ) (hx : x < 2 ^ W) :
    (csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt)).map (fun s => bitSymbol (pairRe s)) =
      (binSyms W x : List (Fin (A + 4))) := by
  simp [csyms, coeffSyms, binSyms, List.map_ofFn, Function.comp_def,
    pairRe_pairSym hA, red, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

theorem bits_realWord (W x : ℕ) (hx : x < 2 ^ W) :
    (binSyms W x : List (Fin (A + 4))).map (fun s => pairSym A (symBit s) false) =
      csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt) := by
  simp [csyms, coeffSyms, binSyms, List.map_ofFn, Function.comp_def,
    red, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

def copyRealBits (width src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix width src dst saved tmp)
    (.seq (moveR dst saved (fun s => bitSymbol (pairRe s))) (moveR saved dst id))

theorem copyRealBits_exec {width src dst saved tmp : Fin T}
    (hreg : [width, src, dst, saved, tmp].Nodup) (hA : 4 ≤ A)
    (W x : ℕ) (hx : x < 2 ^ W) (v : HS T Q A U) (S : Stacks T A)
    (tail : List (Fin (A + 4)))
    (hwidth : (S.R width).length = W)
    (hsrc : S.R src = csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt) ++ tail)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyRealBits width src dst saved tmp) (mk v S) (14 * W + 14)
        (mk v' { S with R := Function.update S.R dst (binSyms W x) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyPrefix_exec (body := body) hreg v S
    (csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt)) tail hsrc (by simpa using hwidth) hsaved htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt)) }
  have he₁' : Exec body (copyPrefix width src dst saved tmp) (mk v S) (10 * W + 10) (mk v₁ S₁) := by
    simpa [hdst, S₁] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body dst saved ‹dst ≠ saved› (fun s => bitSymbol (pairRe s)) v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R dst saved (fun s => bitSymbol (pairRe s)) (S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved dst ‹dst ≠ saved›.symm id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, movedR, hsaved, ‹dst ≠ saved›.symm]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hd : k = dst
    · subst k
      simp [S₂, S₁, movedR, hsaved, ‹dst ≠ saved›, ‹dst ≠ saved›.symm, realWord_bits hA W x hx]
    by_cases hs : k = saved
    · subst k; simp [S₂, S₁, movedR, hsaved, ‹dst ≠ saved›.symm]
    simp [S₂, S₁, movedR, hd, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
