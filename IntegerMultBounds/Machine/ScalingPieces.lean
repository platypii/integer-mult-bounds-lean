import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Arithmetic and stream semantics of splitting a positive unit scaling into
monotone pieces. For modulus Q and fixed positive multiplier c coprime to Q,
the source y belongs to piece floor(c*y/Q). Every output has one admissible
piece and an exact reconstructed source. No tape runtime is asserted here. -/

namespace IntegerMultBounds.Machine.ScalingPieces

/-- Reduced output address. -/
def output (Q c y : ℕ) : ℕ := c * y % Q

/-- The quotient discarded by reduction identifies the source stream. -/
def piece (Q c y : ℕ) : ℕ := c * y / Q

/-- Reconstruct a source address from an output and its selected piece. -/
def restore (Q c z j : ℕ) : ℕ := (z + j * Q) / c

theorem output_lt {Q c y : ℕ} (hQ : 0 < Q) : output Q c y < Q := Nat.mod_lt _ hQ

theorem piece_lt {Q c y : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hy : y < Q) :
    piece Q c y < c := by
  apply (Nat.div_lt_iff_lt_mul hQ).mpr
  exact Nat.mul_lt_mul_of_pos_left hy hc

/-- Exact quotient/remainder identity, without wraparound subtraction. -/
theorem decomposition (Q c y : ℕ) : output Q c y + piece Q c y * Q = c * y := by
  simpa only [output,piece,Nat.mul_comm (c * y / Q) Q] using Nat.mod_add_div (c * y) Q

theorem restore_output {Q c : ℕ} (hc : 0 < c) (y : ℕ) :
    restore Q c (output Q c y) (piece Q c y) = y := by
  rw [restore,decomposition,Nat.mul_div_cancel_left _ hc]

/-- Multiplication by a unit is injective on canonical source addresses. -/
theorem output_injective {Q c : ℕ} (hcop : c.Coprime Q) {x y : ℕ}
    (hx : x < Q) (hy : y < Q) (h : output Q c x = output Q c y) : x = y := by
  have hm : c * x ≡ c * y [MOD Q] := h
  exact (Nat.ModEq.cancel_left_of_coprime hcop.symm hm).eq_of_lt_of_lt hx hy

/-- Every canonical output has a unique canonical source. -/
theorem existsUnique_source {Q c : ℕ} (hQ : 0 < Q) (hcop : c.Coprime Q)
    {z : ℕ} (hz : z < Q) : ∃! y, y < Q ∧ output Q c y = z := by
  let f : Fin Q → Fin Q := fun y => ⟨output Q c y.val,output_lt hQ⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Fin.ext
    exact output_injective hcop x.isLt y.isLt (congrArg Fin.val h)
  obtain ⟨y,hy⟩ := Finite.surjective_of_injective hi ⟨z,hz⟩
  have hyz : output Q c y.val = z := congrArg Fin.val hy
  refine ⟨y.val,⟨y.isLt,hyz⟩,?_⟩
  intro y' hy'
  exact output_injective hcop hy'.1 y.isLt (hy'.2.trans hyz.symm)

/-- An admissible piece is a stream whose affine source reconstruction is integral. -/
def AdmissiblePiece (Q c z j : ℕ) : Prop := j < c ∧ c ∣ z + j * Q

theorem source_piece {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) {y : ℕ} (hy : y < Q) :
    AdmissiblePiece Q c (output Q c y) (piece Q c y) := by
  refine ⟨piece_lt hQ hc hy,?_⟩
  rw [decomposition]
  exact dvd_mul_right c y

/-- Divisibility fixes the exact product before any quotient simplification. -/
theorem restore_product {Q c z j : ℕ} (hj : AdmissiblePiece Q c z j) :
    c * restore Q c z j = z + j * Q := Nat.mul_div_cancel' hj.2

theorem restore_lt {Q c z j : ℕ} (_hc : 0 < c) (hz : z < Q)
    (hj : AdmissiblePiece Q c z j) : restore Q c z j < Q := by
  have hp := restore_product hj
  have hjlt := hj.1
  nlinarith

theorem output_restore {Q c z j : ℕ} (hz : z < Q) (hj : AdmissiblePiece Q c z j) :
    output Q c (restore Q c z j) = z := by
  rw [output,restore_product hj,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hz]

theorem piece_restore {Q c z j : ℕ} (hQ : 0 < Q) (hz : z < Q)
    (hj : AdmissiblePiece Q c z j) : piece Q c (restore Q c z j) = j := by
  rw [piece,restore_product hj,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hz,zero_add]

/-- The merge step selects exactly one stream for each output address. -/
theorem existsUnique_piece {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    {z : ℕ} (hz : z < Q) : ∃! j, AdmissiblePiece Q c z j := by
  obtain ⟨y,⟨hy,hyz⟩,_⟩ := existsUnique_source hQ hcop hz
  refine ⟨piece Q c y,?_,?_⟩
  · rw [← hyz]
    exact source_piece hQ hc hy
  · intro j hj
    have hrest : restore Q c z j = y :=
      output_injective hcop (restore_lt hc hz hj) hy ((output_restore hz hj).trans hyz.symm)
    rw [← hrest,piece_restore hQ hz hj]

/-- On one quotient piece, reduction preserves the strict source order. -/
theorem output_lt_iff {Q c x y : ℕ} (hc : 0 < c) (hpiece : piece Q c x = piece Q c y) :
    output Q c x < output Q c y ↔ x < y := by
  have hx := decomposition Q c x
  have hy := decomposition Q c y
  rw [hpiece] at hx
  constructor <;> intro h <;> nlinarith

/-- Integral reconstruction preserves strict output order within one piece. -/
theorem restore_lt_iff {Q c z w j : ℕ} (hc : 0 < c)
    (hz : AdmissiblePiece Q c z j) (hw : AdmissiblePiece Q c w j) :
    restore Q c z j < restore Q c w j ↔ z < w := by
  have hp := restore_product hz
  have hq := restore_product hw
  constructor <;> intro h <;> nlinarith

/-- Split a source stream by its quotient piece, preserving encounter order,
then replace each address by its scaled output. -/
def stream (Q c j : ℕ) (xs : List ℕ) : List ℕ :=
  (xs.filter (fun y => decide (piece Q c y = j))).map (output Q c)

theorem mem_stream {Q c j z : ℕ} {xs : List ℕ} :
    z ∈ stream Q c j xs ↔ ∃ y ∈ xs, piece Q c y = j ∧ output Q c y = z := by
  simp only [stream,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨y,⟨hy,hp⟩,ho⟩
    exact ⟨y,hy,hp,ho⟩
  · rintro ⟨y,hy,hp,ho⟩
    exact ⟨y,⟨hy,hp⟩,ho⟩

/-- A source-sorted piece is already sorted by its output addresses; it needs no
additional sorting before the multi-stream merge. -/
theorem stream_sorted {Q c j : ℕ} (hc : 0 < c) {xs : List ℕ}
    (hs : xs.Pairwise (· < ·)) : (stream Q c j xs).Pairwise (· < ·) := by
  rw [stream,List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (hs.filter _)
  intro x y hx hy hxy
  have hxj : piece Q c x = j := of_decide_eq_true (List.mem_filter.mp hx).2
  have hyj : piece Q c y = j := of_decide_eq_true (List.mem_filter.mp hy).2
  exact (output_lt_iff hc (hxj.trans hyj.symm)).mpr hxy

/-- The payload's source address is recovered entry-for-entry in every piece. -/
theorem restore_stream {Q c j : ℕ} (hc : 0 < c) (xs : List ℕ) :
    (stream Q c j xs).map (fun z => restore Q c z j) =
      xs.filter (fun y => decide (piece Q c y = j)) := by
  rw [stream,List.map_map]
  calc
    _ = (xs.filter (fun y => decide (piece Q c y = j))).map id := by
      apply List.map_congr_left
      intro y hy
      have hp : piece Q c y = j := of_decide_eq_true (List.mem_filter.mp hy).2
      exact hp ▸ restore_output hc y
    _ = _ := List.map_id _

/-- For the complete input address range, a piece stream contains exactly its
admissible output addresses. -/
theorem mem_range_stream_iff {Q c j z : ℕ} (hQ : 0 < Q) (hc : 0 < c) :
    z ∈ stream Q c j (List.range Q) ↔ z < Q ∧ AdmissiblePiece Q c z j := by
  rw [mem_stream]
  constructor
  · rintro ⟨y,hy,hj,rfl⟩
    refine ⟨output_lt hQ,?_⟩
    rw [← hj]
    exact source_piece hQ hc (List.mem_range.mp hy)
  · rintro ⟨hz,hj⟩
    exact ⟨restore Q c z j,List.mem_range.mpr (restore_lt hc hz hj),
      piece_restore hQ hz hj,output_restore hz hj⟩

/-- The streams partition the complete output address range: no output is lost
or occurs in two different pieces, even when the multiplier exceeds the modulus. -/
theorem existsUnique_output_stream {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) {z : ℕ} (hz : z < Q) :
    ∃! j, z ∈ stream Q c j (List.range Q) := by
  obtain ⟨j,hj,hunique⟩ := existsUnique_piece hQ hc hcop hz
  refine ⟨j,(mem_range_stream_iff hQ hc).mpr ⟨hz,hj⟩,?_⟩
  intro k hk
  exact hunique k ((mem_range_stream_iff hQ hc).mp hk).2

end IntegerMultBounds.Machine.ScalingPieces
