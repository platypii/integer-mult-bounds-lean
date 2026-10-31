module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData

/-! Removing dummy core batches leaves real supplier payloads in core order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- The shifted-slot interface determines the entire real suffix. -/
theorem coreBatchArchive_drop {α : Type*} {N C : ℕ} (hfit : N ≤ C) (width : ℕ)
    (padded : Fin C → List α) (real : Fin N → List α)
    (hlen : ∀ i, (padded i).length = width)
    (hreal : ∀ i, padded (paddedCoreIndex hfit i) = real i) :
    (List.ofFn padded).flatten.drop ((C-N)*width) = (List.ofFn real).flatten := by
  exact paddedArchiveRows_drop (B := 1) hfit (fun i _ => real i) (fun i _ => padded i)
    (fun i _ => hlen i) (fun i _ => hreal i) 0

theorem routedGatherArchive_drop {A s C B : ℕ} (width radius L w : ℕ)
    (hfit : (coreGatherIndices s width radius L).length ≤ C)
    (Fs : List (ZMod s → GaussianInt)) (rows : Fin C → Fin B → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L)
    (hbatches : ∀ i : Fin (coreGatherIndices s width radius L).length,
      (List.ofFn fun j => cstream A w (rows (paddedCoreIndex hfit i) j)).flatten =
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten) :
    ((List.ofFn fun i => (List.ofFn fun j => cstream A w (rows i j)).flatten).flatten).drop
        ((C-(coreGatherIndices s width radius L).length)*(B*(L*w))) =
      (List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten).flatten := by
  apply coreBatchArchive_drop hfit (B*(L*w)) _ _ _ hbatches
  intro i
  simp only [List.length_flatten,List.map_ofFn,Function.comp_def,length_cstream,hlen,
    List.ofFn_const,List.sum_replicate,smul_eq_mul]
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
