module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableLoad

/-! Table initialization commutes with updates outside its owned bank.
The proof is structural in the existing binary-copy list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T A n : ℕ}

private theorem copies_update (D : ℕ) (value : Fin T → ℕ) (rs : List (Fin T × Fin T))
    (k : Fin T) (xs : List (Fin (A+4))) (R : Fin T → List (Fin (A+4)))
    (hoff : ∀ r ∈ rs, r.2 ≠ k) :
    chirpBankCopiesR D value (Function.update R k xs) rs =
      Function.update (chirpBankCopiesR D value R rs) k xs := by
  induction rs generalizing R with
  | nil => rfl
  | cons r rs ih =>
    simp only [chirpBankCopiesR]
    rw [Function.update_of_ne (hoff r (by simp))]
    rw [Function.update_comm (hoff r (by simp)).symm]
    exact ih _ (fun p hp => hoff p (by simp [hp]))

theorem loadedInputTable_update_off (rg : TblR n → Fin T) (input : Fin n → Fin T)
    (D : ℕ) (value : Fin T → ℕ) (S : Stacks T A) (k : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ r, rg r ≠ k) :
    loadedInputTable rg input D value {S with R := Function.update S.R k xs} =
      {loadedInputTable rg input D value S with R :=
        (Function.update (loadedInputTable rg input D value S).R k xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [loadedInputTable,chirpBankLoadR]
  rw [Function.update_comm (hoff .wr).symm,Function.update_comm (hoff .wn).symm]
  apply copies_update
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact hoff (.v i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
