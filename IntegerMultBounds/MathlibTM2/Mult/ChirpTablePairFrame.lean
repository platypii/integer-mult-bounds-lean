module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTablePair
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! # Frames of the generated input/kernel table pair -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node

def chirpTablePairR {T A : ℕ} (R : Regs T A) (input kernel : Fin T)
    (g k : List (Fin (A + 4))) : Regs T A :=
  Function.update (Function.update R input (g ++ R input)) kernel (k ++ R kernel)

/-- The restored generator retains every stack outside its two outputs. -/
theorem chirpTablePairR_off {T A : ℕ} (R : Regs T A) (input kernel : Fin T)
    (g k : List (Fin (A + 4))) (r : Fin T) (hi : r ≠ input) (hk : r ≠ kernel) :
    chirpTablePairR R input kernel g k r = R r := by
  simp only [chirpTablePairR, Function.update_of_ne hi, Function.update_of_ne hk]

theorem chirpTablePairR_input {T A : ℕ} (R : Regs T A) (input kernel : Fin T)
    (g k : List (Fin (A + 4))) (hne : input ≠ kernel) :
    chirpTablePairR R input kernel g k input = g ++ R input := by
  simp only [chirpTablePairR, Function.update_of_ne hne, Function.update_self]

theorem chirpTablePairR_kernel {T A : ℕ} (R : Regs T A) (input kernel : Fin T)
    (g k : List (Fin (A + 4))) :
    chirpTablePairR R input kernel g k kernel = k ++ R kernel := by
  simp only [chirpTablePairR, Function.update_self]

/-- Producing the input table changes only `ys` in the multiplier register file.
The kernel table is outside that file and remains available to the S1 caller. -/
theorem chirpTablePairR_holds {T A : ℕ} {cr : CR → Fin T}
    (hcr : Function.Injective cr) (kernel : Fin T) (hk : ∀ r, cr r ≠ kernel)
    (S : Stacks T A) (ρ : CR → List (Fin (A + 4))) (hS : CHolds cr S ρ)
    (g k : List (Fin (A + 4))) :
    CHolds cr { S with R := chirpTablePairR S.R (cr .ys) kernel g k }
      (Function.update ρ .ys (g ++ ρ .ys)) := by
  intro r
  change chirpTablePairR S.R (cr .ys) kernel g k (cr r) = _
  by_cases hr : r = .ys
  · subst r
    rw [chirpTablePairR_input _ _ _ _ _ (hk .ys), hS .ys, Function.update_self]
  · rw [chirpTablePairR_off _ _ _ _ _ _ (hcr.ne hr) (hk r), Function.update_of_ne hr]
    exact hS r

/-- The input table stream has exactly the consumer's generated G-table shape. -/
theorem chirpScheduledStream_input (A w q s t α m M : ℕ) :
    chirpScheduledStream A w q s t α m M false =
      chirpBlockStream M (fun j => chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (j * m) a)) := by
  simp only [chirpScheduledStream, chirpTableLength, chirpTableOffset, Bool.false_eq_true,
    ite_false]

/-- The kernel table stream has exactly the consumer's shifted K-table shape. -/
theorem chirpScheduledStream_kernel (A w q s t α m M : ℕ) :
    chirpScheduledStream A w q s t α m M true =
      chirpBlockStream M (fun j => chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (j * m) a)) := by
  simp only [chirpScheduledStream, chirpTableLength, chirpTableOffset, ite_true]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
