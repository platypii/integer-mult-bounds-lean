module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseLayout

/-! The ordinary mixed-radix column view is an involutive transpose on
rectangular lists. This gives the return mover its rows from emitted columns. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RectangularColumns
open PaddedFieldLayout PaddedFieldInverseLayout
variable {β : Type}

theorem realColumns_length (M : ℕ) (fill : β) (rows : List (List β)) :
    (realColumns M fill rows).length = M := by simp [realColumns]

theorem realColumns_row_length (M : ℕ) (fill : β) (rows : List (List β)) :
    ∀ col ∈ realColumns M fill rows, col.length = rows.length := by
  intro col hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  simp

theorem realColumns_involutive (M B : ℕ) (fill : β) (rows : List (List β))
    (hB : rows.length = B) (hM : ∀ xs ∈ rows, xs.length = M) :
    realColumns B fill (realColumns M fill rows) = rows := by
  apply List.ext_getElem
  · simp [realColumns,hB]
  · intro i hi hir
    apply List.ext_getElem
    · simp [realColumns,hM _ (List.getElem_mem hir)]
    · intro j hj hjr
      have hjM : j < M := by simpa [realColumns] using hj
      have hrow : (rows[i]).length = M := hM _ (List.getElem_mem hir)
      simp [realColumns,hir,hjM,hrow]

theorem columnRows_transposed {A : ℕ} (encode : β → List (Fin (A+4))) (M B : ℕ) (fill : β)
    (matrices : List (List (List β))) (hcols : ∀ cols ∈ matrices, cols.length = M)
    (hheight : ∀ cols ∈ matrices, ∀ col ∈ cols, col.length = B) :
    columnRows encode M fill (matrices.map (realColumns B fill)) =
      matrices.map (fun cols => cols.flatMap (fun col => col.flatMap encode)) := by
  simp only [columnRows,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro cols hc
  rw [realColumns_involutive B M fill cols (hcols cols hc) (hheight cols hc)]

end IntegerMultBounds.MathlibTM2.Routing.RectangularColumns
