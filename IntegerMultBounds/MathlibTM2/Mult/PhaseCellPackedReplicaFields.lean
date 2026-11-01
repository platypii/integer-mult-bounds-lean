module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedField

/-! Interpret uniformly bounded packed rows as fitting ambient fields. Borrowed
suffixes remain physical suffixes and require no ambient-sized allocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Dropping complete uniform rows exposes the selected row and its own suffix. -/
theorem uniformRows_drop_append {α : Type} (rows : List (List α)) (V n : ℕ)
    (hlen : ∀ row ∈ rows, row.length = V) (hn : n < rows.length) (tail : List α) :
    (rows.flatten++tail).drop (n*V) = rows[n]++((rows.drop (n+1)).flatten++tail) := by
  induction rows generalizing n with
  | nil => simp at hn
  | cons row rows ih =>
    have hr : row.length = V := hlen row (by simp)
    cases n with
    | zero => simp
    | succ n =>
      have he : (n+1)*V = row.length+n*V := by rw [hr]; ring
      rw [he,List.flatten_cons,List.append_assoc,List.drop_length_add_append]
      simpa only [List.getElem_cons_succ,List.drop_succ_cons] using
        ih n (fun z hz => hlen z (by simp [hz])) (by simpa using hn)

theorem encodedRows_packedFields {A s a span w q e : ℕ} [NeZero s]
    (hw : 0 < w) (hfit : a+span ≤ s) (hbudget : q+e+2 ≤ w)
    (rows : List (List (Fin (A+4)))) (hlen : ∀ row ∈ rows, row.length = span*w)
    (hrange : ∀ row ∈ rows, EncodedRange A w q e row) :
    ∃ fields : List (ZMod s → GaussianInt), fields.length = rows.length ∧
      rows = fields.map (fun D => cstream A w (packedInterval a span D)) ∧
      ∀ D ∈ fields, (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (D i)) := by
  induction rows with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons row rows ih =>
    obtain ⟨D,hD,hbound,hfits⟩ := encodedRange_packedField hw hfit hbudget row
      (hlen row (by simp)) (hrange row (by simp))
    obtain ⟨fields,hfields,hrows,hgood⟩ := ih (fun z hz => hlen z (by simp [hz]))
      (fun z hz => hrange z (by simp [hz]))
    refine ⟨D::fields,by simp [hfields],by simp [hD,hrows],?_⟩
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ⟨hbound,hfits⟩
    · exact hgood E hE

theorem packedReplicaFields_read {A s a span q w : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw : 0 < w) (hfit : a+span ≤ s)
    (fields : List (ZMod s → GaussianInt)) (hfits : ∀ D ∈ fields, ∀ i, Fits w (D i))
    (tail : List (Fin (A+4))) (r : Fin fields.length) (i : ZMod s)
    (hi : a ≤ i.val ∧ i.val < a+span) :
    packedIntervalRead q w a
      ((((fields.map (fun D => cstream A w (packedInterval a span D))).flatten)++tail).drop (r.val*span*w)) i =
      value q (fields[r.val] i) := by
  let rows := fields.map (fun D => cstream A w (packedInterval a span D))
  have hlen : ∀ row ∈ rows, row.length = span*w := by
    intro row hrow
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hrow
    simp [length_cstream,packedInterval_length D hfit]
  have hn : r.val < rows.length := by simp [rows]
  have hd := uniformRows_drop_append rows (span*w) r.val hlen hn tail
  rw [Nat.mul_assoc,hd]
  have hr : rows[r.val] = cstream A w (packedInterval a span fields[r.val]) := by simp [rows]
  rw [hr,packedIntervalRead_eq q w a span _ _ [] hfit i hi.1 hi.2]
  exact pairedCellRead_encodedField hA hw _ [] i (hfits _ (List.getElem_mem r.isLt) i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
