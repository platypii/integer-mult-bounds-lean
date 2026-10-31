module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaMajorPaddingData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadGatherPayload

/-! The physically padded gather word supplies the inverse router's complete
row rectangle. Real core rows retain their ambient coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Rows are determined by the actual padding and gathered windows. -/
def paddedGatherRows {s : ℕ} (capacity width radius L : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) : Fin capacity → Fin Fs.length → List GaussianInt :=
  prefixPaddedRows capacity L hcapacity 0 (coreGatherRows width radius L Fs)

@[simp] theorem paddedGatherRows_length {s : ℕ} (capacity width radius L : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin capacity) (j : Fin Fs.length) :
    (paddedGatherRows capacity width radius L hcapacity Fs i j).length = L :=
  prefixPaddedRows_length capacity L hcapacity 0 _ (coreGatherRows_length width radius L Fs) i j

theorem paddedGatherRows_real {s : ℕ} (capacity width radius L : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin (coreGatherIndices s width radius L).length) (j : Fin Fs.length) :
    paddedGatherRows capacity width radius L hcapacity Fs (paddedCoreIndex hcapacity i) j =
      coreGatherRows width radius L Fs i j :=
  prefixPaddedRows_real capacity L hcapacity 0 _ i j

/-- The row view equals the actual physical zero-padded source word. -/
theorem paddedGatherRows_source {A s : ℕ} (capacity width radius L w : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) :
    cstream A w (paddedCoreGatherPayload capacity width radius L Fs) =
      (List.ofFn fun j => cstream A w
        (List.ofFn fun i => paddedGatherRows capacity width radius L hcapacity Fs i j).flatten).flatten := by
  have hrow (j : Fin Fs.length) :
      (List.ofFn fun i => paddedGatherRows capacity width radius L hcapacity Fs i j).flatten =
        tilePrefixPad (capacity*L) 0 (coreGatherPayload width radius L [Fs[j.val]]) := by
    rw [paddedGatherRows,prefixPaddedRows_flatten capacity L hcapacity 0 _ (coreGatherRows_length width radius L Fs),
      coreGatherRows_flatten]
  simp_rw [hrow]
  have hrep := congrArg (List.map (fun F => cstream A w
    (tilePrefixPad (capacity*L) 0 (coreGatherPayload width radius L [F])))) (List.ofFn_get Fs)
  simp only [List.map_ofFn,Function.comp_def,List.get_eq_getElem] at hrep
  rw [hrep]
  simp only [paddedCoreGatherPayload,cstream,←List.flatMap_def,List.flatMap_assoc]

/-- After transpose, each real core's block is the original supplier batch. -/
theorem paddedGatherRows_supplier {A s : ℕ} (capacity width radius L w : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ capacity)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin (coreGatherIndices s width radius L).length) :
    (List.ofFn fun j => cstream A w
      (paddedGatherRows capacity width radius L hcapacity Fs (paddedCoreIndex hcapacity i) j)).flatten =
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten := by
  simp only [paddedGatherRows_real]
  exact coreGatherRows_supplier width radius L w Fs i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
