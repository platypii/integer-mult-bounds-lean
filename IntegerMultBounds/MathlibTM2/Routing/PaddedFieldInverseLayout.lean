module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldLayout

/-! The inverse pads the current real column stream. Its extension is exactly
the zero-column tail of the derived dyadic field, even when field length changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseLayout
open DyadicFieldLayout DyadicFieldMove PaddedFieldLayout
variable {β : Type}

theorem columns_padded_drop (k M : ℕ) (fill : β) (rows : List (List β))
    (hlen : ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k) :
    (columns (rows.map (paddedField k fill))).drop M =
      List.replicate (2^k-M) (List.replicate rows.length fill) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2^k-M
  · have hidx : M+i < 2^k := by omega
    rw [List.getElem?_drop,columns_getElem? _ fill _ hidx,List.getElem?_replicate_of_lt hi]
    apply congrArg some
    simp only [List.map_map,Function.comp_def]
    have hconst : rows.map (fun xs => ((leaves (paddedField k fill xs))[M+i]?).getD fill) = rows.map (fun _ => fill) := by
      apply List.map_congr_left
      intro xs hm
      rw [leaves_paddedField k fill xs (by rw [hlen xs hm]; exact hfit),
        List.getElem?_append_right (by rw [hlen xs hm]; omega),hlen xs hm]
      simp [hi]
    rw [hconst,List.map_const']
  · rw [List.getElem?_eq_none (by simp only [List.length_drop,columns_length]; omega),
      List.getElem?_eq_none (by simp only [List.length_replicate]; omega)]

theorem columns_padded_split (k M : ℕ) (fill : β) (rows : List (List β))
    (hlen : ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k) :
    columns (rows.map (paddedField k fill)) =
      realColumns M fill rows++List.replicate (2^k-M) (List.replicate rows.length fill) := by
  rw [←columns_padded_take k M fill rows hlen hfit,←columns_padded_drop k M fill rows hlen hfit,
    List.take_append_drop]

def columnRows {A : ℕ} (encode : β → List (Fin (A+4))) (M : ℕ) (fill : β)
    (matrices : List (List (List β))) : List (List (Fin (A+4))) :=
  matrices.map fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode)

theorem paddedColumn_word {A : ℕ} (encode : β → List (Fin (A+4))) (k M R : ℕ)
    (fill : β) (zero : Fin (A+4)) (hfill : encode fill = List.replicate R zero)
    (rows : List (List β)) (hlen : ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k) :
    (columns (rows.map (paddedField k fill))).flatMap (fun col => col.flatMap encode) =
      (realColumns M fill rows).flatMap (fun col => col.flatMap encode)++
        List.replicate ((2^k-M)*(rows.length*R)) zero := by
  rw [columns_padded_split k M fill rows hlen hfit,List.flatMap_append]
  simp only [List.flatMap_replicate,hfill,List.flatten_replicate_replicate]

theorem paddedFibers_inverse_input {A : ℕ} (encode : β → List (Fin (A+4))) (k M R B : ℕ)
    (fill : β) (zero : Fin (A+4)) (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k) :
    (finish (paddedFibers k fill matrices)).flatMap (fun rows => rows.flatMap encode) =
      (columnRows encode M fill matrices).flatMap
        (fun xs => xs++List.replicate (2^k*(B*R)-M*(B*R)) zero) := by
  simp only [finish,paddedFibers,columnRows,List.flatMap_map,List.flatMap_assoc]
  apply List.flatMap_congr
  intro rows hm
  rw [paddedColumn_word encode k M R fill zero hfill rows (hlen rows hm) hfit,hrows rows hm,Nat.sub_mul]

theorem columnRows_length {A : ℕ} (encode : β → List (Fin (A+4))) (M : ℕ) (fill : β)
    (matrices : List (List (List β))) : (columnRows encode M fill matrices).length = matrices.length := by
  simp only [columnRows,List.length_map]

theorem columnRows_row_length {A : ℕ} (encode : β → List (Fin (A+4))) (M B R : ℕ)
    (fill : β) (matrices : List (List (List β))) (hencode : ∀ x, (encode x).length = R)
    (hrows : ∀ rows ∈ matrices, rows.length = B) :
    ∀ xs ∈ columnRows encode M fill matrices, xs.length = M*(B*R) := by
  intro xs hm
  obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp hm
  exact (destinationParts_length encode R B 0 M hencode fill rows (hrows rows hr)).1

theorem sourceRows_length {A : ℕ} (encode : β → List (Fin (A+4))) (B : ℕ)
    (matrices : List (List (List β))) (hrows : ∀ rows ∈ matrices, rows.length = B) :
    (sourceRows encode matrices).length = matrices.length*B := by
  rw [sourceRows,List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
  intro rows hm
  simpa only [List.length_map] using hrows rows hm

theorem sourceRows_row_length {A : ℕ} (encode : β → List (Fin (A+4))) (M R : ℕ)
    (matrices : List (List (List β))) (hencode : ∀ x, (encode x).length = R)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) :
    ∀ xs ∈ sourceRows encode matrices, xs.length = M*R := by
  intro xs hx
  obtain ⟨rows,hr,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
  rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro x _; exact hencode x),
    List.sum_replicate,smul_eq_mul,hlen rows hr ys hy]

end IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseLayout
