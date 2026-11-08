module

public import IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates

/-! Row-major storage for a short local field and an arbitrary complete
spectator. Transposition swaps those two fields without changing either index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldOrderLayout
open PaddedFieldLayout
variable {E Γ : Type}

def rows (B M : ℕ) (f : ℕ → ℕ → E) : List (List E) :=
  (List.range B).map fun b => (List.range M).map fun t => f b t

def fibers (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) : List (List (List E)) :=
  (List.range P).map fun a => rows B M (f a)

def stream (encode : E → List Γ) (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) : List Γ :=
  (fibers P B M f).flatMap fun rows => rows.flatMap fun row => row.flatMap encode

theorem rows_length (B M : ℕ) (f : ℕ → ℕ → E) : (rows B M f).length = B := by simp [rows]

theorem row_length (B M : ℕ) (f : ℕ → ℕ → E) (row : List E) (hr : row ∈ rows B M f) :
    row.length = M := by
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  simp

theorem fibers_length (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) : (fibers P B M f).length = P := by
  simp [fibers]

theorem fibers_shape (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) :
    ∀ matrix ∈ fibers P B M f, matrix.length = B ∧ ∀ row ∈ matrix, row.length = M := by
  intro matrix hm
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hm
  exact ⟨rows_length B M (f a),row_length B M (f a)⟩

theorem transpose_rows (fill : E) (B M : ℕ) (f : ℕ → ℕ → E) :
    realColumns M fill (rows B M f) = rows M B (fun t b => f b t) := by
  apply List.ext_getElem
  · simp [realColumns,rows]
  intro t ht ht'
  have htM : t < M := by simpa [realColumns] using ht
  apply List.ext_getElem
  · simp [realColumns,rows]
  intro b hb hb'
  simp [realColumns,rows,htM]

theorem transpose_fibers (fill : E) (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) :
    (fibers P B M f).map (realColumns M fill) = fibers P M B (fun a t b => f a b t) := by
  simp only [fibers,List.map_map,Function.comp_def,transpose_rows]

theorem sourceRows_stream {A : ℕ} (encode : E → List (Fin (A+4)))
    (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) :
    (sourceRows encode (fibers P B M f)).flatten = stream encode P B M f := by
  simp only [sourceRows,stream,List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq]

theorem transposed_stream (encode : E → List Γ) (fill : E) (P B M : ℕ) (f : ℕ → ℕ → ℕ → E) :
    (fibers P B M f).flatMap (fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode)) =
      stream encode P M B (fun a t b => f a b t) := by
  rw [←List.flatMap_map,transpose_fibers]
  rfl

end IntegerMultBounds.MathlibTM2.Routing.FieldOrderLayout
