module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileData

/-! Actual gathered windows form the inverse archive router's row interface.
The RHS list records physical replica order, including the gather's reversal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Preserve ambient coordinates while giving each core/replica pair one row. -/
def coreGatherRows {s : ℕ} (width radius L : ℕ) (Fs : List (ZMod s → GaussianInt))
    (i : Fin (coreGatherIndices s width radius L).length) (j : Fin Fs.length) : List GaussianInt :=
  packedInterval (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L Fs[j.val]

@[simp] theorem coreGatherRows_length {s : ℕ} (width radius L : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin (coreGatherIndices s width radius L).length)
    (j : Fin Fs.length) : (coreGatherRows width radius L Fs i j).length = L := by
  obtain ⟨hleft,hright,hlen⟩ := coreGatherIndices_spec s width radius L _ (List.getElem_mem i.isLt)
  apply packedInterval_length
  omega

private theorem map_get_ofFn {α β : Type*} (xs : List α) (f : α → β) :
    (List.ofFn fun i : Fin xs.length => f xs[i.val]) = xs.map f := by
  simpa only [List.map_ofFn,Function.comp_def,List.get_eq_getElem] using congrArg (List.map f) (List.ofFn_get xs)

/-- This is exactly the replica-major source word consumed by inverse routing. -/
theorem coreGatherPayload_rows {A s : ℕ} (width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) :
    cstream A w (coreGatherPayload width radius L Fs) =
      (List.ofFn fun j : Fin Fs.length => cstream A w
        (List.ofFn fun i => coreGatherRows width radius L Fs i j).flatten).flatten := by
  have hcores (F : ZMod s → GaussianInt) := map_get_ofFn (coreGatherIndices s width radius L)
    (fun k => packedInterval (coreStart width k-radius) L F)
  simp only [coreGatherRows,hcores]
  rw [map_get_ofFn Fs (fun F => cstream A w
    ((coreGatherIndices s width radius L).map (fun k => packedInterval (coreStart width k-radius) L F)).flatten)]
  simp only [coreGatherPayload,cstream,←List.flatMap_def,List.flatMap_assoc]

/-- Inverse routing makes each supplier's entire replica batch contiguous. -/
theorem coreGatherRows_supplier {A s : ℕ} (width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin (coreGatherIndices s width radius L).length) :
    (List.ofFn fun j => cstream A w (coreGatherRows width radius L Fs i j)).flatten =
      cstream A w (Fs.map (packedInterval (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten := by
  rw [show (List.ofFn fun j => cstream A w (coreGatherRows width radius L Fs i j)) =
      Fs.map (fun F => cstream A w (packedInterval
        (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L F)) from
      (by simpa only [coreGatherRows] using (map_get_ofFn Fs
        (fun F => cstream A w (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L F))))]
  simp only [←List.flatMap_def,cstream,List.flatMap_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
