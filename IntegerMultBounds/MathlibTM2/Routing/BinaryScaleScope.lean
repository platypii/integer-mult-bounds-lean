module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScale

/-! A binary scaled copy is produced, used by a framed call, and erased.
The unary exponent and original binary operand are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type}

theorem binaryScale_shifted_binSyms (n L B : ℕ) :
    List.replicate n (bitSymbol false) ++ (binSyms L B : List (Fin (A + 4))) =
      binSyms (n + L) (2 ^ n * B) := by
  rw [binSyms_append, ← binSyms_mod n (2 ^ n * B), Nat.mul_mod_right, binSyms_zero_right,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos n)]

def binaryScaleScope (exponent src dst tmp work : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (binaryScaleProgram exponent src dst tmp work) (.seq call (bclear dst))

theorem binaryScaleScope_exec (body : P → Pr P T Q A U)
    (exponent src dst tmp work output : Fin T) (hreg : [exponent, src, dst, tmp, work, output].Nodup)
    (n L B : ℕ) (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A) (ys : List (Fin (A + 4)))
    (hexponent : (S.R exponent).length = n) (hsrc : S.R src = binSyms L B)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = [])
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update S.R dst (binSyms (n + L) (2 ^ n * B)) }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ price ∧
        Exec body call (mk u C) steps (mk u' { C with R := Function.update C.R output ys })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ price + (8 * (n + L) + 14 : ℕ) ∧
      Exec body (binaryScaleScope exponent src dst tmp work call) (mk v S) steps
        (mk v' { S with R := Function.update S.R output ys }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := binaryScale_exec body exponent src dst tmp work
    (by simp_all) v S hdst htmp hwork
  rw [hsrc, hexponent, length_binSyms, binaryScale_shifted_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R dst (binSyms (n + L) (2 ^ n * B)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R output ys }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) dst v₂ D
  have hlen : (D.R dst).length = n + L := by simp [D, C, ‹dst ≠ output›]
  have hfinal : ({ D with R := Function.update D.R dst [] } : Stacks T A) =
      { S with R := Function.update S.R output ys } := by
    congr 1
    funext r
    simp only [D, C, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hlen, hfinal] at he₃
  refine ⟨v₃, (6 * (L + n) + 12) + (m₂ + (2 * (n + L) + 2)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [hm₂]

end IntegerMultBounds.MathlibTM2.Routing
