module

public import IntegerMultBounds.MathlibTM2.M6.BitOccurrences
public import IntegerMultBounds.MathlibTM2.Layer.VariableRecurrence

/-!
# The variable-rank recurrence of the selected bit supplier

A node of the bit recursion makes one child call per occurrence of the nine-stage list
`BitOccurrences.nineRanks`, of size at most `rank/64` of the parent and weight `1/28416`.
`bit_variable_closed` is the closed bound of `VariableRecurrence.variable_closed_of_rank` for
this list: at every `λ > 1 - a`, `a = 10/5769`, the cost is `O(K^τ e^λ)` plus the leaf term.
The moment is the selected bit bill `BitOccurrences.nine_moment_le`, with its nonnegative
surcharge dropped.

The execution premises `hsize` and `hcost` describe the hosted interchange machine;
they are hypotheses here, as in `VariableRecurrence.t16_variable_closed`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitRecurrence

open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences

/-- Every nine-stage child rank is at most `42`. -/
theorem nineRanks_le (i : Fin nineRanks.length) : nineRanks[i.1] ≤ 42 := by
  have hmem : nineRanks[i.1] ∈ nineRanks := List.getElem_mem i.2
  have hperm := nineRanks_realizes.mem_iff.1 hmem
  simp only [expand, bitHistogram, List.flatMap_cons, List.flatMap_nil, List.mem_append,
    List.mem_replicate, List.not_mem_nil, or_false] at hperm
  omega

/-- The nine-stage moment at `1 - a` is at most one. -/
theorem nine_moment_le_one :
    ∑ i : Fin nineRanks.length, (1 / (28416 : ℝ)) * ((nineRanks[i.1] : ℝ) / 64) ^ (1 - bitSaving)
      ≤ 1 := by
  have h := nine_moment_le
  have hs : 0 ≤ surcharge bitHistogram 64 (1 - bitSaving) := by
    unfold surcharge
    positivity
  have hd : 0 ≤ surcharge bitHistogram 64 (1 - bitSaving) / 28416 := by positivity
  linarith

/-- **PR589 bit recurrence.** A recursion whose internal nodes make one child call per
nine-stage occurrence, of size at most `rank/64` of the parent and weight `1/28416`, with
per-node overhead `C₁ ((K e)^τ + 1)` and leaf cost `C₀ e`, costs at most
`C (K^τ e^λ) + C₀ e^(1-a) u^a` at every `λ > 1 - a`, `a = 10/5769`. -/
theorem bit_variable_closed {Node : Type*}
    (size : Node → ℕ) (child : Node → Fin nineRanks.length → Node)
    (cost : Node → ℝ) (u : ℕ) {τ lam K C₀ C₁ : ℝ}
    (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hlam : 1 - bitSaving < lam) (hK : 1 ≤ K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u)
    (hleaf : ∀ x, size x ≤ u → cost x ≤ C₀ * size x)
    (hsize : ∀ x, u < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((nineRanks[i.1] : ℝ) / 64) * (size x : ℝ))
    (hcost : ∀ x, u < size x →
      cost x ≤ C₁ * ((K * size x) ^ τ + 1) + ∑ i, (1 / (28416 : ℝ)) * cost (child x i)) :
    ∀ x, cost x ≤
      2 * C₁ / (1 - ((42 : ℝ) / 64) ^ (lam - (1 - bitSaving))) * K ^ τ * (size x : ℝ) ^ lam +
      C₀ * (size x : ℝ) ^ (1 - bitSaving) * (u : ℝ) ^ (1 - (1 - bitSaving)) := by
  have ha : bitSaving = 10 / 5769 := rfl
  exact VariableRecurrence.variable_closed_of_rank size (fun _ => nineRanks.length) child
    (fun _ i => nineRanks[i.1]) (fun _ _ => 1 / (28416 : ℝ)) cost u (m := 64) (R := 42)
    (by norm_num) (by norm_num) (by norm_num) hτ hτl (by rw [ha]; norm_num)
    (by rw [ha]; norm_num) hlam hK hC₀ hC₁ hu (fun _ _ => by norm_num)
    (fun _ _ i => by exact_mod_cast nineRanks_le i) hleaf hsize hcost
    (fun _ _ => nine_moment_le_one)

end IntegerMultBounds.MathlibTM2.M6.BitRecurrence
