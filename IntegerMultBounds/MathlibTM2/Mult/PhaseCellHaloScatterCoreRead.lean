module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead

/-! Transfer the solver's packed-row accuracy to the physically published
ambient line, with the same error and original core coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloScatterRows_errorOn {A s : ℕ} [NeZero s] (t band a b L q w : ℕ)
    (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (haloLengthGroup s t band a b L).length*(L*w) ≤ X.length)
    (x : ZMod s → ℝ) (error : ℝ)
    (hlocal : ∀ n : Fin (haloLengthGroup s t band a b L).length, ∀ i : Fin L,
      |(value q (decodeWord ((X.drop ((n.val*L+i.val)*w)).take w))).re -
        x (haloGroupOrigin s t band a b L n+(i.val : ZMod s))| ≤ error)
    (n : Fin (haloLengthGroup s t band a b L).length) :
    PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
      (publishedCellRead q w (0 : ZMod s) (scatterRows (L*w) E X (haloScatterGaps s t band a b L w))) x error := by
  let lo := haloGroupOrigin s t band a b L n
  have hfit : lo.val+L ≤ s := by
    dsimp only [lo]
    rw [haloGroupOrigin_val band a b L n]
    exact haloOrigins_fit s t band a b L _ (List.mem_map.mpr
      ⟨_,haloGroupPhase_mem s t band a b L n,rfl⟩)
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hiL : i < L := Finset.mem_range.mp hi
  have his : i < s := by omega
  have hsum : lo.val+i < s := by omega
  have hval : (lo+(i : ZMod s)).val = lo.val+i := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt his,Nat.mod_eq_of_lt hsum]
  change ‖publishedCellRead q w (0 : ZMod s)
    (scatterRows (L*w) E X (haloScatterGaps s t band a b L w)) (lo+(i : ZMod s)) - x (lo+(i : ZMod s))‖ ≤ error
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero,hval]
  rw [haloScatterRows_word t band a b L w E X hE hX n ⟨i,hiL⟩]
  simpa only [Real.norm_eq_abs] using hlocal n ⟨i,hiL⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
