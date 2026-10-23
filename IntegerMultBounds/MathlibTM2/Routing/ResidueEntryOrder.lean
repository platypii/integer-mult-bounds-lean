module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryGenerate
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.OfFn

/-! Stable residue filtering of a common coordinate-ordered table gives profile
order exactly, rather than merely the same set of entries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem range_filter_residue (d K : ℕ) (hK : 0 < K) (r : Fin K) :
    (List.range (d * K)).filter (fun q => decide (q % K = r.val)) =
      List.ofFn (fun c : Fin d => r.val + c.val * K) := by
  have hleft : ((List.range (d * K)).filter (fun q => decide (q % K = r.val))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hright : (List.ofFn (fun c : Fin d => r.val + c.val * K)).Pairwise (· < ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    have h := Nat.mul_lt_mul_of_pos_right (show i.val < j.val from hij) hK
    omega
  apply hleft.eq_of_mem_iff hright
  intro q
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_ofFn]
  constructor
  · rintro ⟨hq, hr⟩
    refine ⟨⟨q / K, (Nat.div_lt_iff_lt_mul hK).mpr hq⟩, ?_⟩
    change r.val + (q / K) * K = q
    have h := Nat.mod_add_div q K
    nlinarith
  · rintro ⟨c, rfl⟩
    have hmul := Nat.mul_le_mul_right K c.isLt
    constructor
    · have hr := r.isLt
      nlinarith
    · simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]

def matchingTableEntries (N : ℕ) (mate : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range N).map fun q => (q, mate q)

theorem matchingTableEntries_filter_residue (d K : ℕ) (hK : 0 < K) (r : Fin K) (mate : ℕ → ℕ) :
    (matchingTableEntries (d * K) mate).filter (fun x => decide (x.1 % K = r.val)) =
      List.ofFn (fun c : Fin d => (r.val + c.val * K, mate (r.val + c.val * K))) := by
  rw [matchingTableEntries, List.filter_map]
  change ((List.range (d * K)).filter (fun q => decide (q % K = r.val))).map _ = _
  rw [range_filter_residue d K hK r, List.map_ofFn]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
