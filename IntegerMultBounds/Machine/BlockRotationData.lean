import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-! Pure block semantics of controlled cyclic shifts. A fiber is split before
its final a blocks and rejoined suffix first. Payload indices move forward by
a modulo the number of blocks; no tape-runtime assertion is made here. -/

namespace IntegerMultBounds.Machine.BlockRotationData

variable {α : Type*}

/-- Normalize arbitrary offsets, including empty fibers, then split and rejoin. -/
def rotate (a : ℕ) (blocks : List (List α)) : List (List α) :=
  blocks.drop (blocks.length-a%blocks.length) ++ blocks.take (blocks.length-a%blocks.length)

theorem rotate_eq (a : ℕ) (blocks : List (List α)) :
    rotate a blocks = blocks.rotate (blocks.length-a%blocks.length) := by
  exact (List.rotate_eq_drop_append_take (Nat.sub_le _ _)).symm

/-- For an offset less than the block count, the literal split is at Q-a. -/
theorem split_at (a : ℕ) (blocks : List (List α)) (ha : a < blocks.length) :
    rotate a blocks = blocks.drop (blocks.length-a) ++ blocks.take (blocks.length-a) := by
  simp only [rotate,Nat.mod_eq_of_lt ha]

@[simp] theorem rotate_zero (blocks : List (List α)) : rotate 0 blocks = blocks := by
  simp [rotate]

@[simp] theorem rotate_nil (a : ℕ) : rotate a ([] : List (List α)) = [] := by
  simp [rotate]

@[simp] theorem rotate_length (a : ℕ) (blocks : List (List α)) :
    (rotate a blocks).length = blocks.length := by
  rw [rotate_eq,List.length_rotate]

theorem block_perm (a : ℕ) (blocks : List (List α)) : (rotate a blocks).Perm blocks := by
  rw [rotate_eq]
  exact List.rotate_perm _ _

theorem payload_perm (a : ℕ) (blocks : List (List α)) :
    (rotate a blocks).flatten.Perm blocks.flatten := (block_perm a blocks).flatten

@[simp] theorem payload_length (a : ℕ) (blocks : List (List α)) :
    (rotate a blocks).flatten.length = blocks.flatten.length := (payload_perm a blocks).length_eq

private theorem destination_index (a y Q : ℕ) (hy : y < Q) :
    ((y+a)%Q+(Q-a%Q))%Q = y := by
  have hm : a%Q ≤ Q := (Nat.mod_lt a (by omega)).le
  calc
    ((y+a)%Q+(Q-a%Q))%Q = ((y+a%Q)%Q+(Q-a%Q))%Q := by rw [Nat.add_mod_mod]
    _ = (y+a%Q+(Q-a%Q))%Q := Nat.mod_add_mod _ _ _
    _ = (y+Q)%Q := by congr 1; omega
    _ = y := by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hy]

/-- Forward movement: the old block at y occurs at y+a modulo Q. -/
theorem block_destination (a : ℕ) (blocks : List (List α)) (y : ℕ) (hy : y < blocks.length) :
    (rotate a blocks)[(y+a)%blocks.length]'(by
      rw [rotate_length]
      exact Nat.mod_lt _ (by omega)) = blocks[y] := by
  simp only [rotate_eq,List.getElem_rotate]
  congr 1
  exact destination_index a y blocks.length hy

/-- Uniformity includes width zero, so empty payload blocks are allowed. -/
def Uniform (B : ℕ) (blocks : List (List α)) : Prop := ∀ block ∈ blocks, block.length = B

theorem uniform_rotate (a B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    Uniform B (rotate a blocks) := by
  intro block hb
  exact h block ((block_perm a blocks).mem_iff.mp hb)

theorem uniform_volume (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    blocks.flatten.length = blocks.length*B := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
    have hb := h block (by simp)
    have ht : Uniform B blocks := fun b hm => h b (by simp [hm])
    simp only [List.flatten_cons,List.length_append,List.length_cons,ih ht,hb,Nat.add_mul,Nat.one_mul]
    omega

theorem rotated_volume (a B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    (rotate a blocks).flatten.length = blocks.length*B := by
  rw [payload_length,uniform_volume B blocks h]

theorem zero_width (blocks : List (List α)) (h : Uniform 0 blocks) : blocks.flatten = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw [uniform_volume 0 blocks h,Nat.mul_zero]

/-- The block split is exactly a contiguous payload split at B times its block index. -/
theorem payload_split (B cut : ℕ) (blocks : List (List α)) (h : Uniform B blocks)
    (hcut : cut ≤ blocks.length) :
    (blocks.drop cut).flatten ++ (blocks.take cut).flatten =
      blocks.flatten.drop (cut*B) ++ blocks.flatten.take (cut*B) := by
  have ht : Uniform B (blocks.take cut) := fun block hb => h block (List.mem_of_mem_take hb)
  have hl : (blocks.take cut).flatten.length = cut*B := by
    rw [uniform_volume B (blocks.take cut) ht,List.length_take,Nat.min_eq_left hcut]
  have he : (blocks.take cut).flatten ++ (blocks.drop cut).flatten = blocks.flatten := by
    rw [← List.flatten_append,List.take_append_drop]
  rw [← he,← hl]
  simp

/-- Exact flat-tape cut and concatenation performed by a controlled block shift. -/
theorem rotated_payload_split (a B : ℕ) (blocks : List (List α)) (h : Uniform B blocks) :
    (rotate a blocks).flatten =
      blocks.flatten.drop ((blocks.length-a%blocks.length)*B) ++
        blocks.flatten.take ((blocks.length-a%blocks.length)*B) := by
  rw [rotate,List.flatten_append]
  exact payload_split B _ blocks h (Nat.sub_le _ _)

/-- Indexing a fixed-width flattening splits an address into block and payload. -/
theorem flatten_index (B : ℕ) (blocks : List (List α)) (h : Uniform B blocks)
    (y j : ℕ) (hy : y < blocks.length) (hj : j < B) :
    blocks.flatten[y*B+j]? = (blocks[y]'hy)[j]? := by
  induction blocks generalizing y with
  | nil => simp at hy
  | cons block blocks ih =>
    have hb := h block (by simp)
    have ht : Uniform B blocks := fun b hm => h b (by simp [hm])
    cases y with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatten_cons,List.getElem_cons_zero]
      exact List.getElem?_append_left (by omega)
    | succ y =>
      have hyt : y < blocks.length := by simpa using hy
      simp only [List.flatten_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [hb]; simp only [Nat.add_mul,Nat.one_mul]; omega)]
      rw [hb,show (y+1)*B+j-B = y*B+j by simp only [Nat.add_mul,Nat.one_mul]; omega]
      exact ih ht y hyt

/-- Exact flat payload movement, with the coordinate inside each block unchanged. -/
theorem payload_destination (a B : ℕ) (blocks : List (List α)) (h : Uniform B blocks)
    (y j : ℕ) (hy : y < blocks.length) (hj : j < B) :
    (rotate a blocks).flatten[((y+a)%blocks.length)*B+j]? = blocks.flatten[y*B+j]? := by
  rw [flatten_index B (rotate a blocks) (uniform_rotate a B blocks h)
    ((y+a)%blocks.length) j (by rw [rotate_length]; exact Nat.mod_lt _ (by omega)) hj]
  rw [block_destination a blocks y hy,flatten_index B blocks h y j hy hj]

/-- The destination contains the original payload entry, rather than a missing index. -/
theorem payload_destination_entry (a B : ℕ) (blocks : List (List α)) (h : Uniform B blocks)
    (y j : ℕ) (hy : y < blocks.length) (hj : j < B) :
    (rotate a blocks).flatten[((y+a)%blocks.length)*B+j]? =
      some ((blocks[y]'hy)[j]'(by rw [h _ (List.getElem_mem hy)]; exact hj)) := by
  rw [payload_destination a B blocks h y j hy hj,flatten_index B blocks h y j hy hj]
  exact List.getElem?_eq_getElem _

/-- A stream of fibers can select a different fixed offset for every fiber. -/
def rotateFibers (fibers : List (ℕ × List (List α))) : List (List (List α)) :=
  fibers.map (fun f => rotate f.1 f.2)

theorem fiber_destination (fibers : List (ℕ × List (List α))) (i : ℕ) (hi : i < fibers.length) :
    (rotateFibers fibers)[i]'(by simpa [rotateFibers] using hi) =
      rotate (fibers[i]).1 (fibers[i]).2 := by
  simp [rotateFibers]

/-- Rotating each fiber preserves all payloads and the total stream volume. -/
theorem fibers_payload_perm (fibers : List (ℕ × List (List α))) :
    (rotateFibers fibers).flatten.flatten.Perm (fibers.map Prod.snd).flatten.flatten := by
  induction fibers with
  | nil => simp [rotateFibers]
  | cons f fibers ih =>
    simp only [rotateFibers,List.map_cons,List.flatten_cons,List.flatten_append] at ih ⊢
    exact (payload_perm f.1 f.2).append ih

theorem fibers_payload_length (fibers : List (ℕ × List (List α))) :
    (rotateFibers fibers).flatten.flatten.length = (fibers.map Prod.snd).flatten.flatten.length :=
  (fibers_payload_perm fibers).length_eq

end IntegerMultBounds.Machine.BlockRotationData
