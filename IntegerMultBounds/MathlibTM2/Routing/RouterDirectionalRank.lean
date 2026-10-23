module

public import IntegerMultBounds.MathlibTM2.Routing.RouterProfileRank
public import IntegerMultBounds.MathlibTM2.Routing.ShiftedElementarySchedule

/-! Complete directional rank semantics: terminal elementary permutations and
bulk exact-repair maps on one physical field. Uniform tape loading remains separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section
variable (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n)

def routerDirectionalRank (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) : ℕ :=
  routerProfileRanks n K G hK hn X targets source (List.finRange K)
    (shiftedElementaryRankSchedule (routerBorrowed n K G) R
      (routerTerminalTargets n K G targets) source i).val

theorem routerDirectionalRank_bits (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) :
    (fun q : Fin (routerTargetWidth n K G) =>
      (routerDirectionalRank n K G hK hn X R targets source i).testBit
        (routerBorrowed n K G + q.val)) =
      shear targets source (fun q => i.val.testBit (routerBorrowed n K G + q.val)) := by
  have ht : ∀ q ∈ routerTerminalTargets n K G targets,
      source q ∉ routerTerminalTargets n K G targets := by
    intro q hq hs
    exact hsource q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hs).1
  unfold routerDirectionalRank
  rw [routerProfileRanks_bits, shiftedElementaryRankSchedule_bits _ _ _ _ ht]
  rw [← elementaryShears_eq _ _ ht]
  exact router_bulk_terminal_shears_eq n K G hK targets source hsource _

theorem routerDirectionalRank_low (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G)))
    (q : Fin (routerBorrowed n K G)) :
    (routerDirectionalRank n K G hK hn X R targets source i).testBit q.val = i.val.testBit q.val := by
  unfold routerDirectionalRank
  rw [routerProfileRanks_outside n K G hK hn X targets source _ _ _ (Or.inl q.isLt)]
  apply shiftedElementaryRankSchedule_low
  intro t ht hs
  exact hsource t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hs).1

theorem routerDirectionalRank_row (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) :
    routerDirectionalRank n K G hK hn X R targets source i /
        2 ^ (routerBorrowed n K G + routerTargetWidth n K G) =
      i.val / 2 ^ (routerBorrowed n K G + routerTargetWidth n K G) := by
  unfold routerDirectionalRank
  rw [routerProfileRanks_row, shiftedElementaryRankSchedule_row]

theorem routerDirectionalRank_lt (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) :
    routerDirectionalRank n K G hK hn X R targets source i <
      R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mp
  rw [routerDirectionalRank_row]
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr i.isLt

def routerDirectionalFin (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i : Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) :
    Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G)) :=
  ⟨routerDirectionalRank n K G hK hn X R targets source i,
    routerDirectionalRank_lt n K G hK hn X R targets source i⟩

theorem routerDirectionalFin_involutive (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets) :
    Function.Involutive (routerDirectionalFin n K G hK hn X R targets source) := by
  intro i
  let j := routerDirectionalFin n K G hK hn X R targets source i
  have hj := routerDirectionalRank_bits n K G hK hn X R targets source hsource i
  have hk := routerDirectionalRank_bits n K G hK hn X R targets source hsource j
  change (fun q : Fin (routerTargetWidth n K G) => j.val.testBit (routerBorrowed n K G + q.val)) = _ at hj
  rw [hj, shear_involutive targets source hsource] at hk
  apply Fin.ext
  apply eq_of_shifted_bits (routerBorrowed n K G) (routerTargetWidth n K G)
  · intro q
    exact (routerDirectionalRank_low n K G hK hn X R targets source hsource j q).trans
      (routerDirectionalRank_low n K G hK hn X R targets source hsource i q)
  · exact hk
  · exact (routerDirectionalRank_row n K G hK hn X R targets source j).trans
      (routerDirectionalRank_row n K G hK hn X R targets source i)

/-- Complete directional routing is a permutation on every physical address. -/
def routerDirectionalPerm (X R : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets) :
    Equiv.Perm (Fin (R * 2 ^ (routerBorrowed n K G + routerTargetWidth n K G))) where
  toFun := routerDirectionalFin n K G hK hn X R targets source
  invFun := routerDirectionalFin n K G hK hn X R targets source
  left_inv := routerDirectionalFin_involutive n K G hK hn X R targets source hsource
  right_inv := routerDirectionalFin_involutive n K G hK hn X R targets source hsource

end
end IntegerMultBounds.MathlibTM2.Routing
