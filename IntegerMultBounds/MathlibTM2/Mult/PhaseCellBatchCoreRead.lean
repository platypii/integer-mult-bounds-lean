module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! Read one published batch row in its original ambient coordinates. Cropping
the preceding rows introduces no batch-size factor in the core error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

noncomputable def publishedBatchRead {A s : ℕ} (q w n L : ℕ) (lo : ZMod s)
    (ys : List (Fin (A+4))) : ZMod s → ℝ :=
  publishedCellRead q w lo (ys.drop (n*L*w))

theorem publishedBatchRead_errorOn {A s L : ℕ} [NeZero s] (q w n : ℕ) (lo : ZMod s)
    (ys : List (Fin (A+4))) (x : ZMod s → ℝ) (error : ℝ)
    (hfit : lo.val+L ≤ s)
    (hlocal : ∀ i : Fin L, |(value q (decodeWord ((ys.drop ((n*L+i.val)*w)).take w))).re -
      x (lo+(i.val : ZMod s))| ≤ error) :
    PhaseCellInterface.ErrorOn (publishedCellCore lo L) (publishedBatchRead q w n L lo ys) x error := by
  apply publishedCellRead_errorOn q w lo (ys.drop (n*L*w)) x error hfit
  intro i
  simpa only [List.drop_drop, Nat.add_mul] using hlocal i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
