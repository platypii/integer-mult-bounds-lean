module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationAccuracy

/-! Two disjoint length-class sweeps publish the generated owned-core cover.
The result is a physical line with the same uniform error as each packed row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def coreClassOutput {A s : ℕ} (width L w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (E : List (Fin (A+4))) :=
  scatterRows (L*w) E (cstream A w ((corePublicationIndices s width L).map rows).flatten)
    ((corePublicationWindows s width L hw).gaps w)

theorem coreClassOutput_length {A s : ℕ} (width L w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ corePublicationIndices s width L, (rows k).length = L)
    (E : List (Fin (A+4))) (hE : E.length = s*w) :
    (coreClassOutput (s := s) width L w hw rows E).length = s*w := by
  have hlength : ∀ row ∈ (corePublicationIndices s width L).map rows, row.length = L := by
    intro row hr
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hr
    subst row
    exact hrows k hk
  rw [coreClassOutput,length_scatterRows,hE]
  · exact PublicationWindows.gaps_fits _ w E (by omega)
  · simp only [PublicationWindows.gaps_length,corePublicationWindows,List.length_map,
      length_cstream,length_flatten_const _ hlength,Nat.mul_assoc]
    exact le_rfl

def generatedCoreOutput {A s : ℕ} (width w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (E : List (Fin (A+4))) :=
  coreClassOutput (s := s) width (s%width) w hw rows
    (coreClassOutput (s := s) width width w hw rows E)

theorem generatedCoreOutput_error {A s : ℕ} [NeZero s]
    (width q w : ℕ) (hw : 0 < width) (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ coreIndices s width, (rows k).length = coreLength s width k)
    (E : List (Fin (A+4))) (hE : E.length = s*w)
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ coreIndices s width,
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) x error) :
    ∀ i, ‖pairedCellRead q w (generatedCoreOutput (s := s) width w hw rows E) i-x i‖ ≤ error := by
  have hlength (L : ℕ) : ∀ k ∈ corePublicationIndices s width L, (rows k).length = L := by
    intro k hk
    have hk' := (mem_corePublicationIndices s width L k).mp hk
    exact (hrows k hk'.1).trans hk'.2
  have hcert (L : ℕ) : ∀ k ∈ corePublicationIndices s width L,
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) x error := by
    intro k hk
    exact hgood k ((mem_corePublicationIndices s width L k).mp hk).1
  let E₁ := coreClassOutput (s := s) width width w hw rows E
  have hE₁ : E₁.length = s*w := coreClassOutput_length width width w hw rows (hlength width) E hE
  have hx : (corePublicationIndices s width (s%width)).length*((s%width)*w) ≤
      (cstream A w ((corePublicationIndices s width (s%width)).map rows).flatten).length := by
    have hlen : ∀ row ∈ (corePublicationIndices s width (s%width)).map rows, row.length = s%width := by
      intro row hr
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hr
      subst row
      exact hlength _ k hk
    simp only [length_cstream,length_flatten_const _ hlen,List.length_map,Nat.mul_assoc]
    exact le_rfl
  intro i
  obtain ⟨k,hk,hi⟩ := ownedCore_cover width hw i
  rcases coreLength_cases s width k hw hk with hfull | hlast
  · have hk' : k ∈ corePublicationIndices s width width := (mem_corePublicationIndices ..).mpr ⟨hk,hfull⟩
    have hfirst := corePublication_errorOn width width q w hw rows (hlength width) E hE.ge x error (hcert width) k hk'
    have hkeep := corePublication_errorOn_preserves width (s%width) width q w hw
      (Nat.ne_of_lt (Nat.mod_lt s hw)) E₁
      (cstream A w ((corePublicationIndices s width (s%width)).map rows).flatten) hE₁.ge hx k hk' x error hfirst
    exact hkeep i hi
  · have hk' : k ∈ corePublicationIndices s width (s%width) := (mem_corePublicationIndices ..).mpr ⟨hk,hlast⟩
    exact corePublication_errorOn width (s%width) q w hw rows (hlength _) E₁ hE₁.ge x error (hcert _) k hk' i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
