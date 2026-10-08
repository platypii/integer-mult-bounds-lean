import IntegerMultBounds.Machine.BlockRotationData

/-! Pure blockwise coordinate negation. Block zero stays first, the remaining
blocks reverse order, and the payload order inside every block is preserved.
The data recipe reverses the raw tail and then reverses each fixed-width pop. -/

namespace IntegerMultBounds.Machine.BlockNegationData

open BlockRotationData (Uniform)
variable {α : Type*}

def negate : List (List α) → List (List α)
  | [] => []
  | first :: tail => first :: tail.reverse

@[simp] theorem negate_nil : negate ([] : List (List α)) = [] := rfl

@[simp] theorem negate_length (blocks : List (List α)) : (negate blocks).length = blocks.length := by
  cases blocks <;> simp [negate]

@[simp] theorem negate_negate (blocks : List (List α)) : negate (negate blocks) = blocks := by
  cases blocks <;> simp [negate]

theorem block_perm (blocks : List (List α)) : (negate blocks).Perm blocks := by
  cases blocks with
  | nil => rfl
  | cons first tail => exact (List.reverse_perm tail).cons first

theorem payload_perm (blocks : List (List α)) : (negate blocks).flatten.Perm blocks.flatten :=
  (block_perm blocks).flatten

@[simp] theorem payload_length (blocks : List (List α)) :
    (negate blocks).flatten.length = blocks.flatten.length := (payload_perm blocks).length_eq

theorem uniform_negate (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    Uniform B (negate blocks) := fun b hb => h b ((block_perm blocks).mem_iff.mp hb)

theorem volume (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    (negate blocks).flatten.length = blocks.length*B := by
  rw [payload_length,BlockRotationData.uniform_volume B blocks h]

/-- Forward movement by coordinate negation, with block zero fixed. -/
theorem block_destination (blocks : List (List α)) (y : ℕ) (hy : y < blocks.length) :
    (negate blocks)[(blocks.length-y)%blocks.length]'(by
      rw [negate_length]
      exact Nat.mod_lt _ (by omega)) = blocks[y] := by
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem,← List.getElem?_eq_getElem]
  cases blocks with
  | nil => simp at hy
  | cons first tail =>
    cases y with
    | zero => simp [negate]
    | succ y =>
      have hyt : y < tail.length := by simpa using hy
      have hd : (tail.length+1-(y+1))%(tail.length+1) = tail.length-y := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [List.length_cons,hd,negate,List.getElem?_cons_succ]
      have hi : tail.length-y = (tail.length-y-1)+1 := by omega
      rw [hi,List.getElem?_cons_succ,List.getElem?_reverse (by omega)]
      congr 1
      omega

theorem payload_destination (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks)
    (y j : ℕ) (hy : y < blocks.length) (hj : j < B) :
    (negate blocks).flatten[((blocks.length-y)%blocks.length)*B+j]? = blocks.flatten[y*B+j]? := by
  rw [BlockRotationData.flatten_index B (negate blocks) (uniform_negate B blocks h)
    ((blocks.length-y)%blocks.length) j (by rw [negate_length]; exact Nat.mod_lt _ (by omega)) hj]
  rw [block_destination blocks y hy,BlockRotationData.flatten_index B blocks h y j hy hj]

/-- The raw tail reversal also reverses each block's internal payload. -/
def rawBlocks (tail : List (List α)) : List (List α) := tail.reverse.map List.reverse

@[simp] theorem rawBlocks_length (tail : List (List α)) : (rawBlocks tail).length = tail.length := by
  simp [rawBlocks]

theorem rawBlocks_flatten (tail : List (List α)) :
    (rawBlocks tail).flatten = tail.flatten.reverse := by
  simp only [rawBlocks,List.map_reverse,List.reverse_flatten]

theorem rawBlocks_uniform (B : ℕ) (tail : List (List α)) (h : Uniform B tail) :
    Uniform B (rawBlocks tail) := by
  intro b hb
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hb
  simpa using h old (List.mem_reverse.mp hold)

/-- A second reversal inside each popped block restores its payload orientation. -/
theorem corrected_rawBlocks (tail : List (List α)) :
    (rawBlocks tail).map List.reverse = tail.reverse := by
  simp [rawBlocks,List.map_map]

/-- Repeatedly pop exactly B entries and reverse that popped block. The count
controls termination even at width zero, so empty blocks are handled literally. -/
def reversePops (B : ℕ) : ℕ → List α → List α
  | 0, _ => []
  | n+1, stream => (stream.take B).reverse ++ reversePops B n (stream.drop B)

theorem reversePops_flatten (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    reversePops B blocks.length blocks.flatten = (blocks.map List.reverse).flatten := by
  induction blocks with
  | nil => rfl
  | cons first tail ih =>
    have hf := h first (by simp)
    have ht : Uniform B tail := fun b hb => h b (by simp [hb])
    simp only [List.length_cons,List.flatten_cons,reversePops,List.map_cons]
    rw [← hf,List.take_left,List.drop_left,hf,ih ht]

/-- The exact block-pop recipe implements coordinate negation while retaining
the first block and every block's original internal payload order. -/
theorem negation_recipe (B : ℕ) (first : List α) (tail : List (List α)) (h : Uniform B tail) :
    (negate (first::tail)).flatten = first ++ reversePops B tail.length tail.flatten.reverse := by
  rw [← rawBlocks_flatten,← rawBlocks_length tail,
    reversePops_flatten B (rawBlocks tail) (rawBlocks_uniform B tail h),corrected_rawBlocks]
  rfl

end IntegerMultBounds.Machine.BlockNegationData
