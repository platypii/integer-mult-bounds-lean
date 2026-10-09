import IntegerMultBounds.Machine.BinaryAddressOffsetValue

/-! Literal expansion order for an offset table: repeat each row over the
trailing spectator coordinate, then repeat that complete table over preceding
coordinates, including the original dirty back field. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatData

def copies {α : Type*} (xs : List α) : ℕ → List α
  | 0 => []
  | k+1 => copies xs k++xs

@[simp] theorem copies_zero {α : Type*} (xs : List α) : copies xs 0=[] := rfl
@[simp] theorem copies_succ {α : Type*} (xs : List α) (k : ℕ) : copies xs (k+1)=copies xs k++xs := rfl
@[simp] theorem copies_length {α : Type*} (xs : List α) (k : ℕ) : (copies xs k).length=k*xs.length := by
  induction k with
  | zero => simp
  | succ k ih => simp only [copies_succ,List.length_append,ih]; ring

def expanded {α : Type*} (blocks : List (List α)) (L : ℕ) := (blocks.map (fun xs => copies xs L)).flatten

theorem expanded_append {α : Type*} (xs ys : List (List α)) (L : ℕ) :
    expanded (xs++ys) L=expanded xs L++expanded ys L := by simp [expanded]

theorem expanded_succ {α : Type*} (blocks : List (List α)) (L i : ℕ) (hi : i<blocks.length) :
    expanded (blocks.take (i+1)) L=expanded (blocks.take i) L++copies blocks[i] L := by
  rw [List.take_succ_eq_append_getElem hi,expanded_append]
  simp [expanded]

theorem expanded_length {α : Type*} (blocks : List (List α)) (W L : ℕ)
    (hu : BlockRotationData.Uniform W blocks) : (expanded blocks L).length=blocks.length*(L*W) := by
  have hh := BlockRotationData.uniform_volume (L*W) (blocks.map (fun xs => copies xs L)) (by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    rw [copies_length,hu ys hy])
  simpa only [List.length_map,expanded] using hh

def offsets (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) : List (List Bool) :=
  (List.range (2^(n*q))).map (fun i => BinaryAddressOffsetValue.rowWord q b n i hb hbq)

def destination (q b n L K : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  copies (expanded (offsets q b n hb hbq) L) K

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatData
