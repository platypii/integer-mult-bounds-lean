module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Generate a binary zero word at the width of a preserved source, run a
framed call and erase the generated word. No unary width input is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryZeroScope (src zero tmp : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (bzero src zero tmp) (.seq call (bclear zero))

theorem binaryZeroScope_exec (body : P → Pr P T Q A U)
    (src zero tmp output : Fin T) (hreg : [src, zero, tmp, output].Nodup)
    (L : ℕ) (call : Pr P T Q A U) (price : ℝ)
    (v : HS T Q A U) (S : Stacks T A) (ys : List (Fin (A + 4)))
    (hlen : (S.R src).length = L) (hzero : S.R zero = []) (htmp : S.R tmp = [])
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update S.R zero (binSyms L 0) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R output ys })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ (m : ℝ) ≤ price + (6 * L + 6 : ℕ) ∧
      Exec body (binaryZeroScope src zero tmp call) (mk v S) m
        (mk v' { S with R := Function.update S.R output ys }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec (body := body) (wR := src) (c := zero) (t := tmp)
    (by simp_all) v S htmp
  rw [hlen, hzero, List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R zero (binSyms L 0) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R output ys }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) zero v₂ D
  have hdlen : (D.R zero).length = L := by simp [D, C, ‹zero ≠ output›]
  have hfinal : ({ D with R := Function.update D.R zero [] } : Stacks T A) =
      { S with R := Function.update S.R output ys } := by
    congr 1
    funext r
    by_cases hz : r = zero
    · subst r; simp [‹zero ≠ output›, hzero]
    · by_cases ho : r = output <;> simp [D, C, hz, ho, ‹zero ≠ output›.symm]
  rw [hdlen, hfinal] at he₃
  refine ⟨v₃, (4 * L + 4) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith only [hm₂]

end IntegerMultBounds.MathlibTM2.Routing
