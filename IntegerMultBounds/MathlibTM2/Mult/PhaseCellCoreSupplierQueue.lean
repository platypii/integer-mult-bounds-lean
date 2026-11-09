module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows

/-! The existing exposure/router output is exactly the fitting scan's queue.
This is a structural list identity, independent of machine layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix

theorem coreSupplierStream_flatMap {A s : ℕ} (width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) :
    coreSupplierStream A width radius L w Fs =
      (coreGatherIndices s width radius L).flatMap (fun k =>
        cstream A w (Fs.map (packedInterval (coreStart width k-radius) L)).flatten) := by
  let jobs := coreGatherIndices s width radius L
  let row := fun k => cstream A w (Fs.map (packedInterval (coreStart width k-radius) L)).flatten
  have hrows : (List.ofFn fun j : Fin jobs.length => row jobs[j.val]) = jobs.map row := by
    simpa only [List.map_ofFn,Function.comp_def,List.get_eq_getElem] using
      congrArg (List.map row) (List.ofFn_get jobs)
  change (List.ofFn fun j : Fin jobs.length => row jobs[j.val]).flatten = jobs.flatMap row
  rw [hrows,List.flatMap_def]

theorem coreSupplierStream_attach {A s : ℕ} (width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) :
    coreSupplierStream A width radius L w Fs =
      (coreGatherIndices s width radius L).attach.flatMap (fun c =>
        cstream A w (Fs.map (packedInterval (coreStart width c.val-radius) L)).flatten) := by
  rw [coreSupplierStream_flatMap]
  simp only [List.flatMap_def]
  exact congrArg List.flatten (List.attach_map_val (l := coreGatherIndices s width radius L)
    (f := fun k => cstream A w (Fs.map (packedInterval (coreStart width k-radius) L)).flatten)).symm

theorem coreOriginQueue_attach {A s : ℕ} (width radius L V : ℕ) :
    (coreGatherIndices s width radius L).flatMap (fun k => binSyms (A := A) V (coreStart width k-radius)) =
      (coreGatherIndices s width radius L).attach.flatMap (fun c => binSyms V (coreStart width c.val-radius)) := by
  simp only [List.flatMap_def]
  exact congrArg List.flatten (List.attach_map_val (l := coreGatherIndices s width radius L)
    (f := fun k => binSyms (A := A) V (coreStart width k-radius))).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
