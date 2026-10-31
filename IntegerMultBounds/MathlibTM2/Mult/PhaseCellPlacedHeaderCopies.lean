module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Transport structural header copying through an injective destination bank.
The proof is over an arbitrary copy list; concrete header roles come last. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {m n T A : ℕ}

theorem unaryCopiesR_project (src : Fin m → Fin T) (dst : Fin n → Fin T)
    (hdst : Function.Injective dst) (value : Fin T → ℕ) (σ : Fin m → ℕ)
    (rs : List (Fin m × Fin n))
    (hvalue : ∀ r ∈ rs, value (src r.1) = σ r.1) (R : Regs T A) :
    unaryCopiesR value R (rs.map (fun r => (src r.1,dst r.2))) ∘ dst =
      unaryCopiesR σ (R ∘ dst) rs := by
  induction rs generalizing R with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,unaryCopiesR]
    rw [ih (fun p hp => hvalue p (by simp [hp]))]
    congr 1
    funext k
    simp [Function.comp_apply,Function.update_apply,hdst.eq_iff,hvalue r (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
