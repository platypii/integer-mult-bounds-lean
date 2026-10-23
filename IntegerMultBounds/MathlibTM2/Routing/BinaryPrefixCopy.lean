module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Host.BinArithBits

/-! Copy a binary register at a smaller width using a live width template.
The source, width template and scratch tapes are restored exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def binaryPrefixCopyProgram (width src dst saved tmp : Fin T) : Pr P T Q A U :=
  copyPrefix width src dst saved tmp

theorem binaryPrefixCopy_exec (body : P → Pr P T Q A U)
    (width src dst saved tmp : Fin T) (hreg : [width, src, dst, saved, tmp].Nodup)
    (L W x : ℕ) (hWL : W ≤ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms L x) (hwidth : (S.R width).length = W)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (binaryPrefixCopyProgram width src dst saved tmp) (mk v S) (10 * W + 10)
        (mk v' { S with R := Function.update S.R dst (binSyms W x ++ S.R dst) }) := by
  have hsplit : S.R src = binSyms W x ++ binSyms (L - W) (x / 2 ^ W) := by
    rw [hsrc, ← binSyms_append]
    congr 1
    omega
  obtain ⟨v', hu, hx⟩ := copyPrefix_exec (body := body) hreg v S (binSyms W x)
    (binSyms (L - W) (x / 2 ^ W)) hsplit (by simpa using hwidth) hsaved htmp
  rw [length_binSyms] at hx
  exact ⟨v', hu, hx⟩

end IntegerMultBounds.MathlibTM2.Routing
