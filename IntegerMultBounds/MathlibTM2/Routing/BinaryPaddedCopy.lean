module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Copy an operand and append high zeros from two preserved length sources.
The final one-bit padding guarantees room for subsequent addition and carry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryPaddedCopyProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) (rg 3) (rg 4) (rg 5))
    (.seq (bpad (rg 3) (rg 1) (rg 4) (rg 5)) (bpad (rg 3) (rg 2) (rg 4) (rg 5)))

theorem binaryPaddedCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L M x : ℕ) (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L x)
    (hpadding : (S.R (rg 1)).length = M) (hone : (S.R (rg 2)).length = 1)
    (hblank : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → i ≠ 2 → S.R (rg i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryPaddedCopyProgram rg) (mk v S) (14*L+10*M+28)
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms (L+M+1) x) }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := bcopy_exec body (a := rg 0) (c := rg 3) (t₁ := rg 4) (t₂ := rg 5)
    (by simp [List.nodup_cons,hrg.eq_iff]) v S
    (hblank 4 (by decide) (by decide) (by decide)) (hblank 5 (by decide) (by decide) (by decide))
  rw [hsrc,hblank 3 (by decide) (by decide) (by decide),List.append_nil,length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms L x) }
  obtain ⟨v₂,hu₂,he₂⟩ := bpad_exec (body := body) (a := rg 3) (eR := rg 1) (t₁ := rg 4) (t₂ := rg 5)
    (by simp [List.nodup_cons,hrg.eq_iff]) hx v₁ C (by simp [C])
    (by simp [C,hrg.eq_iff,hblank 4 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 5 (by decide) (by decide) (by decide)])
  have hp : (C.R (rg 1)).length = M := by simpa [C,hrg.eq_iff] using hpadding
  rw [hp] at he₂
  let D : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms (L+M) x) }
  have hd : ({ C with R := Function.update C.R (rg 3) (binSyms (L+M) x) } : Stacks T A) = D := by simp [C,D]
  rw [hd] at he₂
  have hx' : x < 2 ^ (L+M) := hx.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
  obtain ⟨v₃,hu₃,he₃⟩ := bpad_exec (body := body) (a := rg 3) (eR := rg 2) (t₁ := rg 4) (t₂ := rg 5)
    (by simp [List.nodup_cons,hrg.eq_iff]) hx' v₂ D (by simp [D])
    (by simp [D,hrg.eq_iff,hblank 4 (by decide) (by decide) (by decide)])
    (by simp [D,hrg.eq_iff,hblank 5 (by decide) (by decide) (by decide)])
  have ho : (D.R (rg 2)).length = 1 := by simpa [D,hrg.eq_iff] using hone
  rw [ho] at he₃
  have hf : ({ D with R := Function.update D.R (rg 3) (binSyms (L+M+1) x) } : Stacks T A) =
      { S with R := Function.update S.R (rg 3) (binSyms (L+M+1) x) } := by simp [D]
  rw [hf] at he₃
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  exact ⟨v₃,hu₃.trans (hu₂.trans hu₁),Exec.cast he (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
