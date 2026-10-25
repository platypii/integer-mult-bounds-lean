module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead

/-! Transfer the solver's packed-row accuracy to the physically published
ambient line, with the same error and original core coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalScatterRows_errorOn {A s : ℕ} [NeZero s] (t band L q w : ℕ)
    (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (naturalLengthGroup s t band L).length*(L*w) ≤ X.length)
    (x : ZMod s → ℝ) (error : ℝ)
    (hlocal : ∀ n : Fin (naturalLengthGroup s t band L).length, ∀ i : Fin L,
      |(value q (decodeWord ((X.drop ((n.val*L+i.val)*w)).take w))).re -
        x (naturalGroupOrigin s t band L n+(i.val : ZMod s))| ≤ error)
    (n : Fin (naturalLengthGroup s t band L).length) :
    PhaseCellInterface.ErrorOn (publishedCellCore (naturalGroupOrigin s t band L n) L)
      (publishedCellRead q w (0 : ZMod s) (scatterRows (L*w) E X (naturalScatterGaps s t band L w))) x error := by
  let lo := naturalGroupOrigin s t band L n
  have hfit : lo.val+L ≤ s := by
    dsimp only [lo]
    rw [naturalGroupOrigin_val band L n]
    exact naturalOrigins_fit s t band L _ (List.mem_map.mpr
      ⟨_,naturalGroupPhase_mem s t band L n,rfl⟩)
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hiL : i < L := Finset.mem_range.mp hi
  have his : i < s := by omega
  have hsum : lo.val+i < s := by omega
  have hval : (lo+(i : ZMod s)).val = lo.val+i := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt his,Nat.mod_eq_of_lt hsum]
  change ‖publishedCellRead q w (0 : ZMod s)
    (scatterRows (L*w) E X (naturalScatterGaps s t band L w)) (lo+(i : ZMod s)) - x (lo+(i : ZMod s))‖ ≤ error
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero,hval]
  rw [naturalScatterRows_word t band L w E X hE hX n ⟨i,hiL⟩]
  simpa only [Real.norm_eq_abs] using hlocal n ⟨i,hiL⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
