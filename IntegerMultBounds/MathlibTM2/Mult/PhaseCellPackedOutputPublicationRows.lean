module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPair

/-! Recover publication rows from the actual class output certificate, including
the per-job byte identity needed when the result tape stores jobs in reverse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s t B L : ℕ} [NeZero s] [NeZero t]


/-- The physical handoff volume follows from the certified rectangular shape. -/
theorem Rows.stream_length {batch : PackedExactBatch A s t B L} (rows : batch.Rows) :
    rows.stream.length = batch.records.length*(B*(L*batch.W)) := by
  have hrow (i : Fin batch.records.length) :
      ((List.ofFn fun j => cstream A batch.W (rows.values i j)).flatten).length = B*(L*batch.W) := by
    rw [length_flatten_const _ (by
      intro word hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      rw [length_cstream,rows.length]),List.length_ofFn]
  rw [Rows.stream,length_flatten_const _ (by
    intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hrow i),List.length_ofFn]

theorem rows_of_outputs (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs) :
    ∃ rows : batch.Rows, outputs = List.ofFn (fun i => (List.ofFn fun j => cstream A batch.W (rows.values i j)).flatten) := by
  obtain ⟨batches,houtputs,hrows⟩ := PackedNormalizedJob.outputs_rows batch.W batch.hwidth hgood
  have hN := hrows.length_eq
  have hjob (i : Fin batch.records.length) : (batch.records[i.val]).RowOutput
      (batches[i.val]'(by rw [←hN]; exact i.isLt)) := hrows.get i.isLt (by rw [←hN]; exact i.isLt)
  have hcount (i : Fin batch.records.length) :
      (batches[i.val]'(by rw [←hN]; exact i.isLt)).length = B :=
    (hjob i).1.trans (batch.hreplicas _ (List.getElem_mem i.isLt))
  let values := fun (i : Fin batch.records.length) (j : Fin B) =>
    (batches[i.val]'(by rw [←hN]; exact i.isLt))[j.val]'(by rw [hcount]; exact j.isLt)
  have hrow (i : Fin batch.records.length) : List.ofFn (values i) =
      batches[i.val]'(by rw [←hN]; exact i.isLt) := by
    apply List.ext_getElem (by simp only [List.length_ofFn,hcount])
    intro j hj hj'
    simp only [List.getElem_ofFn,values]
  have hview : List.ofFn (fun i => List.ofFn (values i)) = batches := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact hN)
    intro i hi hi'
    simp only [List.getElem_ofFn,hrow]
  have hlength (i : Fin batch.records.length) (j : Fin B) : (values i j).length = L := by
    have hh := (hjob i).2.1 _ (List.getElem_mem (show j.val <
      (batches[i.val]'(by rw [←hN]; exact i.isLt)).length by rw [hcount]; exact j.isLt))
    exact hh.trans (batch.hcore _ (List.getElem_mem i.isLt))
  have hcert (i : Fin batch.records.length) : (batch.records.get i).ExactRowOutput
      (batch.J (batch.records.get i)) (List.ofFn (values i)) := by
    have hi := List.getElem_mem i.isLt
    let r := batch.records[i.val]
    letI : NeZero r.t := ⟨by rw [show r.t = t from batch.ht _ hi]; exact NeZero.ne t⟩
    have hh := (hjob i).exact_inverse r (batch.hp _ hi) (batch.htarget _ hi) (batch.hlocal _ hi)
      (batch.J r) (by simpa only [r,show r.t = t from batch.ht _ hi] using batch.hJ _ hi)
    simpa only [r,List.get_eq_getElem,hrow] using hh
  let rows : batch.Rows := ⟨values,hlength,hcert⟩
  refine ⟨rows,?_⟩
  have hencode (rs : List (List GaussianInt)) : cstream A batch.W rs.flatten =
      (rs.map (cstream A batch.W)).flatten := by
    simpa only [List.flatMap_id,List.flatMap,List.map_id,id_eq] using
      cstream_flatMap_rows (A := A) (w := batch.W) rs id
  rw [houtputs,←hview]
  simp only [List.map_ofFn,Function.comp_def,hencode,rows]

theorem rows_of_reversed_outputs (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs) :
    ∃ rows : batch.Rows,
      outputs.flatten = rows.stream ∧
      outputs.reverse.flatten = (List.ofFn (fun i =>
        (List.ofFn fun j => cstream A batch.W (rows.values i j)).flatten)).reverse.flatten := by
  obtain ⟨rows,hwords⟩ := rows_of_outputs batch outputs hgood
  exact ⟨rows,by rw [hwords]; rfl,by rw [hwords]⟩

/-- The actual result-tape volume is fixed by the certified rectangular batch. -/
theorem outputs_volume (batch : PackedExactBatch A s t B L)
    (outputs : List (List (Fin (A+4))))
    (hgood : List.Forall₂ PackedNormalizedJob.output batch.records outputs) :
    outputs.reverse.flatten.length = batch.records.length*(B*(L*batch.W)) := by
  obtain ⟨rows,hflat,_⟩ := rows_of_reversed_outputs batch outputs hgood
  calc
    outputs.reverse.flatten.length = outputs.flatten.length := by
      simp only [List.length_flatten,List.map_reverse,List.sum_reverse]
    _ = rows.stream.length := congrArg List.length hflat
    _ = _ := rows.stream_length

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
