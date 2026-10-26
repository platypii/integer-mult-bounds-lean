module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.SchurBlockSolve
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! The published physical words carry the numerical halo selection contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem publishedHalo_accuracy {A q w s t band a b eD eC : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hDwidth : q+eD+2 ≤ w) (hCwidth : q+eC+2 ≤ w)
    (D C : ZMod s → GaussianInt)
    (hD : ∀ i ∈ haloInterior s t band a b, ‖value q (D i)‖ ≤ (2 : ℝ)^eD)
    (hC : ∀ i ∈ haloBoundary s t band a b, ‖value q (C i)‖ ≤ (2 : ℝ)^eC)
    (x : ZMod s → ℝ) (error : ℝ)
    (herror : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (SchurDominance.glue (haloInterior s t band a b)
        (fun i => (value q (D i)).re) (fun i => (value q (C i)).re)) x error)
    (tail : List (Fin (A+4))) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s G)++tail) i) x error := by
  dsimp only
  let G := fun i => realPartWord (publicationField t band a b D C i)
  intro i hi
  have hfit : Fits w (G i) := by
    by_cases hI : i ∈ haloInterior s t band a b
    · apply fits_of_value_power (q := q) (e := eD) hDwidth
      rw [value_realPartWord_norm]
      exact (Complex.abs_re_le_norm _).trans (by simpa [G,publicationField,hI] using hD i hI)
    · have hB : i ∈ haloBoundary s t band a b := Finset.mem_sdiff.mpr ⟨hi,hI⟩
      apply fits_of_value_power (q := q) (e := eC) hCwidth
      rw [value_realPartWord_norm]
      exact (Complex.abs_re_le_norm _).trans (by simpa [G,publicationField,hI] using hC i hB)
  have hw : 0 < w := by omega
  have hread : publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s G)++tail) i =
      (value q (G i)).re := by
    simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
    rw [cstream_word w (chirpLine s G) tail i.val (by simpa using i.val_lt)]
    simp only [chirpLine,List.getElem_map,List.getElem_range,ZMod.natCast_zmod_val]
    rw [decodeWord_of_fits hA hw _ hfit]
  change ‖publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s G)++tail) i-x i‖ ≤ error
  rw [hread]
  by_cases hI : i ∈ haloInterior s t band a b
  · simpa [G,publicationField,SchurDominance.glue,hI] using herror i hi
  · simpa [G,publicationField,SchurDominance.glue,hI] using herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
