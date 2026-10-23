module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Test a live binary value for zero, constructing and erasing the comparison
operand internally. Every tape is restored; the scan slot records the result. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryZeroTestProgram (src zero tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bzero src zero tx) (.seq (beq src zero tx ty tz cy) (bclear zero))

theorem binaryZeroTest_exec (body : P → Pr P T Q A U)
    (src zero tx ty tz cy : Fin T) (hregs : [src, zero, tx, ty, tz].Nodup)
    (hcsrc : cy ≠ src) (hczero : cy ≠ zero) (L x : ℕ) (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hzero : S.R zero = []) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (x = 0)) ∧
      Exec body (binaryZeroTestProgram src zero tx ty tz cy) (mk v S) (14 * L + 14) (mk v' S) := by
  have hn := hregs
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec body (wR := src) (c := zero) (t := tx)
    (by regs_nodup) v S htx
  rw [hsrc, length_binSyms, hzero, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R zero (binSyms L 0) }
  obtain ⟨v₂, hu₂, hc₂, _, he₂⟩ := beq_exec body
    (a := src) (b := zero) (tx := tx) (ty := ty) (tz := tz) (cy := cy)
    hregs hcsrc hczero hx (by positivity : 0 < 2 ^ L) v₁ S₁
    (by simp [S₁, ‹src ≠ zero›, hsrc]) (by simp [S₁])
    (by simp [S₁, Ne.symm ‹zero ≠ tx›, htx]) (by simp [S₁, Ne.symm ‹zero ≠ ty›, hty])
    (by simp [S₁, Ne.symm ‹zero ≠ tz›, htz])
  obtain ⟨v₃, hu₃, hs₃, he₃⟩ := bclear_exec body zero v₂ S₁
  have hf : Function.update S₁.R zero [] = S.R := by simp [S₁, hzero]
  have hz : S₁.R zero = binSyms L 0 := by simp [S₁]
  rw [hf, hz, length_binSyms] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), by rw [hs₃]; exact hc₂, ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
