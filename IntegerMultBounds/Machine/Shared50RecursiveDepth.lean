import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
import IntegerMultBounds.Machine.RecursiveRoleChildCallSetup

/-! Dimension facts for the actual power-width recursion. Splitting the node's
rows once, then entering a selected cross child with divisor one, consumes
exactly one factor of the World count and one power of the width radix. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveDepth
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open RecursiveInterchangeLayout (Descriptor role child volume)

/-- All dimension premises of a recursive node, with arbitrary positive
spectator factors. The row condition is the manuscript's W^depth condition. -/
structure Shape (depth : ℕ) (v : Descriptor) : Prop where
  positive : v.Positive
  width : v.width = 125000^depth
  rows : roleCount^depth ∣ v.rows

theorem rows_iff_W (depth : ℕ) (v : Descriptor) :
    roleCount^depth ∣ v.rows ↔ Shared50Parameters.W^depth ∣ v.rows := by
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W]

theorem roleCount_positive : 0 < roleCount := by decide

theorem of_W {depth : ℕ} {v : Descriptor} (hp : v.Positive)
    (hw : v.width = 125000^depth) (hd : Shared50Parameters.W^depth ∣ v.rows) :
    Shape depth v := ⟨hp,hw,(rows_iff_W depth v).mpr hd⟩

theorem base_width {v : Descriptor} (h : Shape 0 v) : v.width = 1 := by
  simpa only [pow_zero] using h.width

theorem recurse_width {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    1 < v.width := by
  rw [h.width,pow_succ]
  have hp : 0 < (125000 : ℕ)^depth := pow_pos (by decide) _
  omega

theorem split_divides {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    roleCount ∣ v.rows :=
  dvd_trans (by rw [pow_succ]; exact dvd_mul_left _ _) h.rows

theorem split_positive {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    (role v roleCount).Positive :=
  RecursiveRowsNodeLayout.role_positive _ _ roleCount_positive h.positive (split_divides h)

theorem split_width {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    (role v roleCount).width = 125000*(125000^depth) := by
  change v.width = _
  rw [h.width,pow_succ,Nat.mul_comm]

/-- The exact descriptor constructed by the same-row physical call setup. -/
def selected (depth : ℕ) (v : Descriptor) (i j : Fin 125000) : Descriptor :=
  child prime 1 (125000^depth) (role v roleCount) i j

theorem selected_eq (depth : ℕ) (v : Descriptor) (i j : Fin 125000) :
    selected depth v i j = child prime roleCount (125000^depth) v i j :=
  RecursiveRowsNodeLayout.child_role _ _ _ _ _ _

theorem selected_shape {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) : Shape depth (selected depth v i j) := by
  rw [selected_eq]
  exact ⟨RecursiveInterchangeLayout.child_positive _ _ _ _ _ _
      Shared50ModularControl.prime_prime.pos roleCount_positive (split_divides h) h.positive,
    rfl,RecursiveInterchangeLayout.child_rows_divisible _ _ _ _ _ _ _ roleCount_positive h.rows⟩

/-- No second row quotient is taken at child entry. -/
theorem selected_rows (depth : ℕ) (v : Descriptor) (i j : Fin 125000) :
    (selected depth v i j).rows = (role v roleCount).rows := by
  simp [selected,child]

theorem split_rows {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v) :
    roleCount^depth ∣ (role v roleCount).rows := by
  have hd := (selected_shape h (0 : Fin 125000) (0 : Fin 125000)).rows
  rw [selected_rows] at hd
  exact hd

/-- The runtime volume is exactly one role stream, rather than the parked
ancestor bank or the full unsplit parent. -/
theorem selected_volume_role {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) :
    volume prime (selected depth v i j) = volume prime (role v roleCount) :=
  RecursiveAffineViews.cross_volume _ _ _ _ _ (split_width h)

theorem selected_volume {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) :
    volume prime (selected depth v i j) = volume prime v/roleCount := by
  rw [selected_eq]
  apply RecursiveInterchangeLayout.child_volume_div _ _ _ _ _ _ _ roleCount_positive (split_divides h)
  rw [h.width,pow_succ,Nat.mul_comm]

theorem selected_volume_W {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) :
    volume prime (selected depth v i j) = volume prime v/Shared50Parameters.W := by
  rw [selected_volume h,Shared50RecursiveNodeLayout.roleCount_eq_W]

/-- Both occupied descriptor sets in the matching return are bounded by the
same child volume. This requires no extra assumptions on spectator sizes. -/
theorem return_header_lengths {depth : ℕ} {v : Descriptor} (h : Shape (depth+1) v)
    (i j : Fin 125000) (old current : Fin 6 → List Bool)
    (ho : RecursiveDimensionBank.Headers (role v roleCount) old)
    (hc : RecursiveDimensionBank.Headers (selected depth v i j) current) :
    (∀ z, (old z).length ≤ 2*volume prime (selected depth v i j)) ∧
      (∀ z, (current z).length ≤ 2*volume prime (selected depth v i j)) := by
  have hp := (selected_shape h i j).positive
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le _ hp
  constructor
  · intro z
    have hl := RecursiveAffinePrepare.header_log Shared50ModularControl.prime_prime.two_le
      _ (split_positive h) old ho z
    rw [← selected_volume_role h i j] at hl
    have hn := Nat.log2_le_self (volume prime (selected depth v i j))
    omega
  · intro z
    have hl := RecursiveAffinePrepare.header_log Shared50ModularControl.prime_prime.two_le
      _ hp current hc z
    have hn := Nat.log2_le_self (volume prime (selected depth v i j))
    omega

end
end IntegerMultBounds.Machine.Shared50RecursiveDepth
