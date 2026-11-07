module

public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldMove
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedFiberPadding

/-! Derive the balanced field view from actual padded rows. No array or routing
witness is supplied: structural take/drop packing reconstructs the row exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PaddedFieldLayout
open DyadicFieldLayout DyadicFieldMove
variable {β : Type}

def leaves : {k : ℕ} → Field β k → List β
  | 0, x => [x]
  | _+1, x => leaves x.1++leaves x.2

def pack (k : ℕ) (fill : β) (xs : List β) : Field β k :=
  match k with
  | 0 => xs.headD fill
  | k+1 => (pack k fill (xs.take (2^k)),pack k fill (xs.drop (2^k)))

theorem leaves_length {k : ℕ} (x : Field β k) : (leaves x).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [leaves,List.length_append,ih,Nat.pow_succ]; omega

theorem leaves_pack (k : ℕ) (fill : β) (xs : List β) (hlen : xs.length = 2^k) :
    leaves (pack k fill xs) = xs := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,Nat.pow_zero] at hlen; omega)
      subst xs
      rfl
  | succ k ih =>
    have ht : (xs.take (2^k)).length = 2^k := by rw [List.length_take,hlen,Nat.pow_succ]; omega
    have hd : (xs.drop (2^k)).length = 2^k := by rw [List.length_drop,hlen,Nat.pow_succ]; omega
    simp only [pack,leaves,ih _ ht,ih _ hd,List.take_append_drop]

theorem word_eq_leaves {A : ℕ} (encode : β → List (Fin (A+4))) {k : ℕ} (x : Field β k) :
    word encode x = (leaves x).flatMap encode := by
  induction k with
  | zero => simp [word,leaves]
  | succ k ih => simp only [word,leaves,List.flatMap_append,ih]

def paddedField (k : ℕ) (fill : β) (xs : List β) : Field β k :=
  pack k fill (xs++List.replicate (2^k-xs.length) fill)

theorem leaves_paddedField (k : ℕ) (fill : β) (xs : List β) (hfit : xs.length ≤ 2^k) :
    leaves (paddedField k fill xs) = xs++List.replicate (2^k-xs.length) fill := by
  apply leaves_pack
  simp only [List.length_append,List.length_replicate]
  omega

/-- The actual symbol padding supplies the exact input word required by the
binary field mover, with the block view determined by the original row. -/
theorem word_paddedField {A : ℕ} (encode : β → List (Fin (A+4))) (k R : ℕ)
    (fill : β) (zero : Fin (A+4)) (hfill : encode fill = List.replicate R zero)
    (xs : List β) (hfit : xs.length ≤ 2^k) :
    word encode (paddedField k fill xs) = xs.flatMap encode++List.replicate ((2^k-xs.length)*R) zero := by
  rw [word_eq_leaves,leaves_paddedField k fill xs hfit,List.flatMap_append,
    List.flatMap_replicate,hfill,List.flatten_replicate_replicate]

/-- The binary recursion enumerates ordinary column indices in increasing order. -/
theorem columns_getElem? {k : ℕ} (rows : List (Field β k)) (fill : β) (i : ℕ) (hi : i < 2^k) :
    (columns rows)[i]? = some (rows.map fun x => ((leaves x)[i]?).getD fill) := by
  induction k generalizing i with
  | zero =>
    have hi0 : i = 0 := by simpa only [Nat.pow_zero,Nat.lt_one_iff] using hi
    subst i
    simp [columns,leaves]
  | succ k ih =>
    simp only [columns]
    by_cases hic : i < 2^k
    · rw [List.getElem?_append_left (by rw [columns_length]; exact hic),ih _ i hic]
      simp only [List.map_map,Function.comp_def]
      apply congrArg some
      apply List.map_congr_left
      intro x _
      simp only [leaves]
      rw [List.getElem?_append_left (l₁ := leaves x.1) (l₂ := leaves x.2) (i := i)
        (by rw [leaves_length]; exact hic)]
    · have hig : 2^k ≤ i := by omega
      have hir : i-2^k < 2^k := by rw [Nat.pow_succ] at hi; omega
      rw [List.getElem?_append_right (by rw [columns_length]; exact hig),columns_length,ih _ _ hir]
      simp only [List.map_map,Function.comp_def]
      apply congrArg some
      apply List.map_congr_left
      intro x _
      simp only [leaves]
      rw [List.getElem?_append_right (l₁ := leaves x.1) (l₂ := leaves x.2) (i := i)
        (by rw [leaves_length]; exact hig),leaves_length]

def realColumns (M : ℕ) (fill : β) (rows : List (List β)) : List (List β) :=
  List.ofFn fun i : Fin M => rows.map fun xs => (xs[i.val]?).getD fill

/-- Cropping the padded field at its destination gives the mixed-radix
transpose of the real rows, rather than an inverse using obsolete bit names. -/
theorem columns_padded_take (k M : ℕ) (fill : β) (rows : List (List β))
    (hlen : ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k) :
    (columns (rows.map (paddedField k fill))).take M = realColumns M fill rows := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < M
  · rw [List.getElem?_take_of_lt hi,columns_getElem? _ fill i (hi.trans_le hfit)]
    simp only [realColumns,List.getElem?_ofFn,hi,↓reduceDIte,List.map_map,Function.comp_def]
    apply congrArg some
    apply List.map_congr_left
    intro xs hm
    rw [leaves_paddedField k fill xs (by rw [hlen xs hm]; exact hfit),
      List.getElem?_append_left (by rw [hlen xs hm]; exact hi)]
  · simp [realColumns,hi]

def paddedFibers (k : ℕ) (fill : β) (matrices : List (List (List β))) : List (List (Field β k)) :=
  matrices.map fun rows => rows.map (paddedField k fill)

def sourceRows {A : ℕ} (encode : β → List (Fin (A+4))) (matrices : List (List (List β))) :
    List (List (Fin (A+4))) := matrices.flatMap fun rows => rows.map fun xs => xs.flatMap encode

theorem paddedFibers_input {A : ℕ} (encode : β → List (Fin (A+4))) (k M R : ℕ)
    (fill : β) (zero : Fin (A+4)) (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M)
    (hfit : M ≤ 2^k) :
    stream encode (paddedFibers k fill matrices) =
      (sourceRows encode matrices).flatMap (fun xs => xs++List.replicate (2^k*R-M*R) zero) := by
  simp only [stream,paddedFibers,sourceRows,List.flatMap_map,List.flatMap_assoc]
  apply List.flatMap_congr
  intro rows hm
  apply List.flatMap_congr
  intro xs hx
  rw [word_paddedField encode k R fill zero hfill xs (by rw [hlen rows hm xs hx]; exact hfit),
    hlen rows hm xs hx,Nat.sub_mul]

theorem columns_row_length {k : ℕ} (rows : List (Field β k)) :
    ∀ col ∈ columns rows, col.length = rows.length := by
  induction k with
  | zero =>
    intro col hm
    have hc : col = rows := by simpa only [columns,List.mem_singleton] using hm
    subst col
    rfl
  | succ k ih =>
    intro col hm
    simp only [columns,List.mem_append] at hm
    rcases hm with hm | hm
    · simpa only [List.length_map] using ih (rows.map Prod.fst) col hm
    · simpa only [List.length_map] using ih (rows.map Prod.snd) col hm

/-- The exact prefix kept by destination cropping, followed by its owned tail. -/
def destinationParts {A : ℕ} (encode : β → List (Fin (A+4))) (k M : ℕ) (fill : β)
    (rows : List (List β)) : List (Fin (A+4)) × List (Fin (A+4)) :=
  ((realColumns M fill rows).flatMap (fun col => col.flatMap encode),
    ((columns (rows.map (paddedField k fill))).drop M).flatMap (fun col => col.flatMap encode))

theorem paddedFibers_output {A : ℕ} (encode : β → List (Fin (A+4))) (k M : ℕ) (fill : β)
    (matrices : List (List (List β))) (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M)
    (hfit : M ≤ 2^k) :
    (finish (paddedFibers k fill matrices)).flatMap (fun rows => rows.flatMap encode) =
      SmallFieldMove.pairStream (matrices.map (destinationParts encode k M fill)) := by
  simp only [finish,paddedFibers,List.flatMap_map,List.flatMap_assoc,SmallFieldMove.pairStream]
  apply List.flatMap_congr
  intro rows hm
  simp only [destinationParts]
  rw [←columns_padded_take k M fill rows (hlen rows hm) hfit,←List.flatMap_append,List.take_append_drop]

theorem destinationParts_length {A : ℕ} (encode : β → List (Fin (A+4))) (R B k M : ℕ)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (rows : List (List β))
    (hrows : rows.length = B) :
    (destinationParts encode k M fill rows).1.length = M*(B*R) ∧
      (destinationParts encode k M fill rows).2.length = (2^k-M)*(B*R) := by
  have hr : ∀ col ∈ realColumns M fill rows, col.length = B := by
    intro col hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    simpa only [List.length_map] using hrows
  have hd : ∀ col ∈ (columns (rows.map (paddedField k fill))).drop M, col.length = B := by
    intro col hm
    have hh := columns_row_length (rows.map (paddedField k fill)) col (List.mem_of_mem_drop hm)
    simpa only [List.length_map,hrows] using hh
  constructor
  · have hh := stream_length (k := 0) encode R B hencode (realColumns M fill rows) hr
    simpa only [destinationParts,stream,word,realColumns,List.length_ofFn,Nat.pow_zero,Nat.one_mul] using hh
  · have hh := stream_length (k := 0) encode R B hencode ((columns (rows.map (paddedField k fill))).drop M) hd
    simpa only [destinationParts,stream,word,List.length_drop,columns_length,Nat.pow_zero,Nat.one_mul] using hh

end IntegerMultBounds.MathlibTM2.Routing.PaddedFieldLayout
