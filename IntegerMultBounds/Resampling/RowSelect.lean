import IntegerMultBounds.Machine.OrderedSelect
import IntegerMultBounds.Machine.GrowingCounterData
import IntegerMultBounds.NLogN.ResamplingInverse

/-! The row-selecting map `C` of the resampling interface on tapes. With the
addend `2s`, the modulus `2t` and the initial counter `2t - s - 1`, the
ordered selection machine copies exactly the records at the indices
`[tj/s]`, `0 ≤ j < s`, in increasing order: the counter crosses a multiple
of `2t` before record `i` exactly when `i` is such an index. One pass over
the `t` records costs the input volume plus a fixed multiple of `log t` per
record, with no numerical error. -/

namespace IntegerMultBounds.Resampling.RowSelect

open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.OrderedSelect
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.NLogN (rowIndexNat nearest)

/-! ### The index identity -/

section Index

/-- `[tj/s]` as a natural-number division. -/
def q (s t j : ℕ) : ℕ := (2 * (t * j) + s) / (2 * s)

theorem q_eq_iff (s t j i : ℕ) (hs : 0 < s) :
    q s t j = i ↔ 2 * (s * i) ≤ 2 * (t * j) + s ∧ 2 * (t * j) + s < 2 * (s * i) + 2 * s := by
  have h2s : 0 < 2 * s := by omega
  rw [q, le_antisymm_iff, Nat.le_div_iff_mul_le h2s, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul h2s]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith

/-- The indices are strictly increasing. -/
theorem q_strictMono (s t j k : ℕ) (hs : 0 < s) (hst : s < t) (hjk : j < k) : q s t j < q s t k := by
  have h2s : 0 < 2 * s := by omega
  have hk : 2 * (t * j) + s + 2 * s ≤ 2 * (t * k) + s := by nlinarith
  calc q s t j < q s t j + 1 := Nat.lt_succ_self _
    _ = (2 * (t * j) + s + 2 * s) / (2 * s) := (Nat.add_div_right _ h2s).symm
    _ ≤ q s t k := Nat.div_le_div_right hk

theorem q_lt (s t j : ℕ) (hs : 0 < s) (hst : s < t) (hj : j < s) : q s t j < t := by
  have h2s : 0 < 2 * s := by omega
  rw [q, Nat.div_lt_iff_lt_mul h2s]
  have : t * j + t ≤ t * s := by nlinarith
  nlinarith

/-- The counter crosses a multiple of `2t` before record `i` exactly when `i`
is a selected index. -/
theorem crossing_iff (s t i : ℕ) (hs : 0 < s) (hst : s < t) (hi : i < t) :
    2 * t ≤ (2 * t - s - 1 + 2 * (s * i)) % (2 * t) + 2 * s ↔ ∃ j < s, q s t j = i := by
  have h2t : 0 < 2 * t := by omega
  set x := 2 * t - s - 1 + 2 * (s * i) with hx
  have hx' : x + s + 1 = 2 * t + 2 * (s * i) := by omega
  have hQ : s * i + s ≤ s * t := by nlinarith
  constructor
  · intro h
    have hdm := Nat.div_add_mod x (2 * t)
    rw [mul_assoc] at hdm
    have hm := Nat.mod_lt x h2t
    refine ⟨x / (2 * t), ?_, ?_⟩
    · have hc : s * t = t * s := mul_comm _ _
      have hP : t * (x / (2 * t)) < t * s := by omega
      exact Nat.lt_of_mul_lt_mul_left hP
    · rw [q_eq_iff _ _ _ _ hs]
      constructor <;> omega
  · rintro ⟨j, hj, hq⟩
    rw [q_eq_iff _ _ _ _ hs] at hq
    have hrep : x = (x - 2 * (t * j)) + 2 * t * j := by rw [mul_assoc]; omega
    rw [hrep, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The paper's row index is `q`. -/
theorem rowIndexNat_eq (s t j : ℕ) (hs : 0 < s) (hj : j < s) :
    rowIndexNat s t (j : ZMod s) = q s t j := by
  have : NeZero s := ⟨by omega⟩
  unfold rowIndexNat q nearest
  rw [ZMod.val_natCast_of_lt hj]
  have hreal : (t : ℝ) * j / s + 1 / 2 = ((2 * (t * j) + s : ℕ) : ℝ) / ((2 * s : ℕ) : ℝ) := by
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  rw [hreal, Int.floor_div_natCast, Int.floor_natCast, ← Int.natCast_div, Int.toNat_natCast]

end Index

/-! ### Filtering a range by a strictly increasing enumeration -/

section Lists

theorem eq_of_pairwise_lt {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l => exact absurd ((hm b).mpr (List.mem_cons_self)) List.not_mem_nil
  | cons a l ih =>
    cases l₂ with
    | nil => exact absurd ((hm a).mp List.mem_cons_self) List.not_mem_nil
    | cons b l' =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        have ha : a ∈ b :: l' := (hm a).mp List.mem_cons_self
        have hb : b ∈ a :: l := (hm b).mpr List.mem_cons_self
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · rcases List.mem_cons.mp hb with rfl | hb
          · rfl
          · have := h₁.1 b hb
            have := h₂.1 a ha
            omega
      subst hab
      congr 1
      refine ih h₁.2 h₂.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem _ hx)) with rfl | h
        · exact absurd (h₁.1 x hx) (lt_irrefl _)
        · exact h
      · rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem _ hx)) with rfl | h
        · exact absurd (h₂.1 x hx) (lt_irrefl _)
        · exact h

/-- Filtering `range t` by membership in a strictly increasing enumeration
below `t` gives the enumeration. -/
theorem filter_range_eq_map (f : ℕ → ℕ) (s t : ℕ) (hmono : ∀ j k, j < k → k < s → f j < f k)
    (hlt : ∀ j, j < s → f j < t) :
    (List.range t).filter (fun i => decide (∃ j < s, f j = i)) = (List.range s).map f := by
  refine eq_of_pairwise_lt (List.pairwise_lt_range.filter _) ?_ fun x => ?_
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun {j k} _ hk hjk =>
      hmono j k hjk (List.mem_range.mp hk)
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨-, j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hlt j hj, j, hj, rfl⟩

variable {a : ℕ}

theorem selected_eq_filter (recs : List (List (Fin (a + 4)))) (S T R0 : List Bool) (n : ℕ) :
    selected recs S T R0 n =
      ((List.range n).filter (fun i => sel S T R0 i)).map (fun i => recs.getD i []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [selected_succ, ih, List.range_succ, List.filter_append, List.map_append]
    by_cases h : sel S T R0 n = true <;> simp [h]

end Lists

/-! ### The selection machine with the resampling constants -/

section Machine

variable {a : ℕ}

/-- The addend `2s`. -/
def twoS (s : ℕ) : List Bool := GrowingCounterData.advance (2 * s) []
/-- The modulus `2t`. -/
def twoT (t : ℕ) : List Bool := GrowingCounterData.advance (2 * t) []
/-- The initial counter `2t - s - 1`. -/
def R0 (s t : ℕ) : List Bool := GrowingCounterData.advance (2 * t - s - 1) []

theorem twoS_value (s : ℕ) : value (twoS s) = 2 * s := GrowingCounterData.empty_value _
theorem twoT_value (t : ℕ) : value (twoT t) = 2 * t := GrowingCounterData.empty_value _
theorem R0_value (s t : ℕ) : value (R0 s t) = 2 * t - s - 1 := GrowingCounterData.empty_value _

/-- A word of value below `2t` is no wider than the modulus word. -/
theorem width_le (t n : ℕ) (hn : n < 2 * t) :
    (GrowingCounterData.advance n []).length ≤ (twoT t).length + 1 := by
  have h1 := GrowingCounterData.empty_width n
  have h2 := Counter.value_lt (twoT t)
  rw [twoT_value] at h2
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [GrowingCounterData.advance]
  · have : n.log2 < (twoT t).length := (Nat.log2_lt hpos.ne').mpr (by omega)
    omega

variable (s t : ℕ) (hs : 0 < s) (hst : s < t)

include hs hst in
theorem sel_iff (i : ℕ) (hi : i < t) :
    sel (twoS s) (twoT t) (R0 s t) i = decide (∃ j < s, q s t j = i) := by
  rw [sel_eq (twoS s) (twoT t) (R0 s t) (by rw [twoS_value, twoT_value]; omega) (by rw [R0_value, twoT_value]; omega)
    (width_le t _ (by omega)) (width_le t _ (by omega)) i, twoS_value, twoT_value, R0_value]
  by_cases h : 2 * t ≤ (2 * t - s - 1 + 2 * s * i) % (2 * t) + 2 * s
  · have h' := (crossing_iff s t i hs hst hi).mp (by rw [mul_assoc] at h; exact h)
    simp [h, h']
  · have h' : ¬ ∃ j < s, q s t j = i := fun hc =>
      h (by rw [mul_assoc]; exact (crossing_iff s t i hs hst hi).mpr hc)
    simp [h, h']

include hs hst in
/-- The selected records are those at the indices `[tj/s]`, in order. -/
theorem selected_eq (recs : List (List (Fin (a + 4)))) :
    selected recs (twoS s) (twoT t) (R0 s t) t =
      (List.range s).map (fun j : ℕ => recs.getD (rowIndexNat s t (j : ZMod s)) []) := by
  rw [selected_eq_filter, List.filter_congr (fun i hi => sel_iff s t hs hst i (List.mem_range.mp hi)),
    filter_range_eq_map (q s t) s t (fun j k hjk hk => q_strictMono s t j k hs hst hjk)
      (fun j hj => q_lt s t j hs hst hj), List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp, rowIndexNat_eq s t j hs (List.mem_range.mp hj)]

include hs hst in
/-- The row-selecting map on tapes: from the `t` records, the output receives the
records at `[tj/s]`, `0 ≤ j < s`, in order, within the input volume plus a fixed
multiple of the modulus width per record. -/
theorem rowSelect_hoare (recs : List (List (Fin (a + 4)))) (hlen : recs.length = t)
    (hrec : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) (pO pR pS pT pF : ℤ) :
    HoareTime (OrderedSelect.program (a := a))
      (fun v => v = bank (inTape recs) (fun _ => blank)
        (putWord (fun _ => blank) pR ((R0 s t).map bitSymbol))
        (putWord (fun _ => blank) pS ((twoS s).map bitSymbol))
        (putWord (fun _ => blank) pT ((twoT t).map bitSymbol)) (fun _ => blank) 0 pO pR pS pT pF)
      (fun v => v = bank (inTape recs)
        (putWord (fun _ => blank) pO
          (flat ((List.range s).map (fun j : ℕ => recs.getD (rowIndexNat s t (j : ZMod s)) []))))
        (putWord (fun _ => blank) pR ((rWord (twoS s) (twoT t) (R0 s t) t).map bitSymbol))
        (putWord (fun _ => blank) pS ((twoS s).map bitSymbol))
        (putWord (fun _ => blank) pT ((twoT t).map bitSymbol)) (fun _ => blank)
        ((flat recs).length : ℤ)
        (pO + (flat ((List.range s).map (fun j : ℕ => recs.getD (rowIndexNat s t (j : ZMod s)) []))).length)
        pR pS pT pF)
      ((flat recs).length + t * (10 * (twoT t).length + 52)) := by
  have h := select_hoare recs (twoS s) (twoT t) (R0 s t) pO pR pS pT pF
    (by rw [twoS_value, twoT_value]; omega) (by rw [R0_value, twoT_value]; omega)
    (width_le t _ (by omega)) (width_le t _ (by omega)) hrec
  refine h.consequence (fun v hv => ?_) (fun v hv => ?_) ?_
  · rw [hv]; simp [X, selected, rWord, flat_nil, start_zero, putWord]
  · rw [hv, X, start_length, hlen, selected_eq s t hs hst recs]
  · have := cost_le recs (twoT t)
    rw [hlen] at this
    rw [hlen]
    exact this

end Machine

end IntegerMultBounds.Resampling.RowSelect
