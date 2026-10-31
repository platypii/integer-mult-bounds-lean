module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRowExactInverse
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! A rectangular view of actual packed schedule output. Indexing the existing
row lists changes neither their bytes nor their numerical certificates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem packedCoreTileRows {B L : ℕ} (W : ℕ) (records : List (PackedNormalizedJob A s))
    (batches : List (List (List GaussianInt)))
    (J : PackedNormalizedJob A s → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (h : List.Forall₂ (fun r rows => r.ExactRowOutput (J r) rows) records batches)
    (hcount : ∀ r ∈ records, r.Fs.length = B)
    (hcore : ∀ r ∈ records, coreLength s r.coreWidth r.k = L) :
    ∃ tileRows : Fin records.length → Fin B → List GaussianInt,
      (∀ i j, (tileRows i j).length = L) ∧
      (batches.map (fun rows => cstream A W rows.flatten)).flatten =
        (List.ofFn fun i => (List.ofFn fun j => cstream A W (tileRows i j)).flatten).flatten ∧
      ∀ i : Fin records.length, records[i].ExactRowOutput (J records[i]) (List.ofFn (tileRows i)) := by
  have hlength := h.length_eq
  have hjob (i : Fin records.length) : records[i].ExactRowOutput (J records[i])
      (batches[i.val]'(by rw [←hlength]; exact i.isLt)) := h.get i.isLt (by rw [←hlength]; exact i.isLt)
  have hbatchCount (i : Fin records.length) :
      (batches[i.val]'(by rw [←hlength]; exact i.isLt)).length = B :=
    (hjob i).1.trans (hcount _ (List.getElem_mem i.isLt))
  let tileRows := fun (i : Fin records.length) (j : Fin B) =>
    (batches[i.val]'(by rw [←hlength]; exact i.isLt))[j.val]'(by rw [hbatchCount]; exact j.isLt)
  have hrow (i : Fin records.length) : List.ofFn (tileRows i) =
      batches[i.val]'(by rw [←hlength]; exact i.isLt) := by
    apply List.ext_getElem (by simp only [List.length_ofFn,hbatchCount])
    intro j hj hj'
    simp only [List.getElem_ofFn,tileRows]
  have hview : List.ofFn (fun i => List.ofFn (tileRows i)) = batches := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact hlength)
    intro i hi hi'
    simp only [List.getElem_ofFn,hrow]
  have hencode (rows : List (List GaussianInt)) :
      cstream A W rows.flatten = (rows.map (cstream A W)).flatten := by
    simpa only [List.flatMap_id,List.flatMap,List.map_id,id_eq] using cstream_flatMap_rows (A := A) (w := W) rows id
  refine ⟨tileRows,?_,?_,?_⟩
  · intro i j
    have hlen := (hjob i).2.1 _ (List.getElem_mem (show j.val < (batches[i.val]'(by rw [←hlength]; exact i.isLt)).length by
      rw [hbatchCount]; exact j.isLt))
    exact hlen.trans (hcore _ (List.getElem_mem i.isLt))
  · rw [←hview]
    simp only [List.map_ofFn,Function.comp_def,hencode]
  · intro i
    rw [hrow]
    exact hjob i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
