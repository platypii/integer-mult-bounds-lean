module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorWords

/-! Interpret a published row in the original ambient coordinates and transfer
its coordinate bound to the shared S3-S5 core-error interface. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def publishedCellCore {s : ℕ} (lo : ZMod s) (L : ℕ) : Finset (ZMod s) :=
  (Finset.range L).image (fun i : ℕ => lo + (i : ZMod s))

noncomputable def publishedCellRead {A s : ℕ} (q w : ℕ) (lo : ZMod s) (ys : List (Fin (A + 4))) (k : ZMod s) : ℝ :=
  (value q (decodeWord ((ys.drop ((k.val - lo.val) * w)).take w))).re

/-- A nonwrapping ambient row uses its original coordinate as its word index. -/
theorem publishedCell_offset {s L i : ℕ} [NeZero s] (lo : ZMod s)
    (hfit : lo.val + L ≤ s) (hi : i < L) :
    (lo + (i : ZMod s)).val - lo.val = i := by
  have his : i < s := by omega
  have hsum : lo.val + i < s := by omega
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt his, Nat.mod_eq_of_lt hsum]
  omega

/-- No cardinality factor is introduced when publishing the row on its core. -/
theorem publishedCellRead_errorOn {A s L : ℕ} [NeZero s] (q w : ℕ) (lo : ZMod s)
    (ys : List (Fin (A + 4))) (x : ZMod s → ℝ) (error : ℝ)
    (hfit : lo.val + L ≤ s)
    (hlocal : ∀ i : Fin L, |(value q (decodeWord ((ys.drop (i.val * w)).take w))).re -
      x (lo + (i.val : ZMod s))| ≤ error) :
    PhaseCellInterface.ErrorOn (publishedCellCore lo L) (publishedCellRead q w lo ys) x error := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  have hiL : i < L := Finset.mem_range.mp hi
  simpa only [publishedCellRead, publishedCell_offset lo hfit hiL, Real.norm_eq_abs] using
    hlocal ⟨i, hiL⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
