module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPaddedCopy

/-! Two operands of different widths gain preserved copies at a common width
with one extra carry bit. Original operands and the one-bit padding source restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryCrossPadSlot (j : Fin 2) : Fin 6 → Fin 7 :=
  if j = 0 then ![0,1,2,3,5,6] else ![1,0,2,4,5,6]
theorem binaryCrossPadSlot_injective (j : Fin 2) : Function.Injective (binaryCrossPadSlot j) := by
  fin_cases j <;> decide +kernel

def binaryCrossPadProgram (rg : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (binaryPaddedCopyProgram (rg ∘ binaryCrossPadSlot 0))
    (binaryPaddedCopyProgram (rg ∘ binaryCrossPadSlot 1))

theorem binaryCrossPad_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (L M x y : ℕ)
    (hx : x < 2 ^ L) (hy : y < 2 ^ M) (v : HS T Q A U) (S : Stacks T A)
    (hsrcX : S.R (rg 0) = binSyms L x) (hsrcY : S.R (rg 1) = binSyms M y)
    (hone : (S.R (rg 2)).length = 1)
    (hblank : ∀ i : Fin 7, i ≠ 0 → i ≠ 1 → i ≠ 2 → S.R (rg i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCrossPadProgram rg) (mk v S) (24*(L+M)+56)
        (mk v' { S with R := (Function.update (Function.update S.R (rg 3) (binSyms (L+M+1) x))
          (rg 4) (binSyms (L+M+1) y)) }) := by
  have off : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 2 →
      binaryCrossPadSlot j i ≠ 0 ∧ binaryCrossPadSlot j i ≠ 1 ∧ binaryCrossPadSlot j i ≠ 2 := by
    decide +kernel
  obtain ⟨v₁,hu₁,he₁⟩ := binaryPaddedCopy_exec body (rg ∘ binaryCrossPadSlot 0)
    (hrg.comp (binaryCrossPadSlot_injective 0)) L M x hx v S hsrcX
    (by rw [show (rg ∘ binaryCrossPadSlot 0) 1 = rg 1 from rfl,hsrcY,length_binSyms]) hone
    (by intro i h0 h1 h2; have h := off 0 i h0 h1 h2; exact hblank _ h.1 h.2.1 h.2.2)
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms (L+M+1) x) }
  have keep (i : Fin 6) : C.R ((rg ∘ binaryCrossPadSlot 1) i) = S.R ((rg ∘ binaryCrossPadSlot 1) i) := by
    apply Function.update_of_ne
    exact hrg.ne (by fin_cases i <;> decide)
  obtain ⟨v₂,hu₂,he₂⟩ := binaryPaddedCopy_exec body (rg ∘ binaryCrossPadSlot 1)
    (hrg.comp (binaryCrossPadSlot_injective 1)) M L y hy v₁ C
    ((keep 0).trans hsrcY)
    (by rw [keep 1,show (rg ∘ binaryCrossPadSlot 1) 1 = rg 0 from rfl,hsrcX,length_binSyms])
    ((congrArg List.length (keep 2)).trans hone)
    (by intro i h0 h1 h2; have h := off 1 i h0 h1 h2; exact (keep i).trans (hblank _ h.1 h.2.1 h.2.2))
  rw [Nat.add_comm M L] at he₂
  have he := Exec.seq he₁ he₂
  exact ⟨v₂,hu₂.trans hu₁,Exec.cast he (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
