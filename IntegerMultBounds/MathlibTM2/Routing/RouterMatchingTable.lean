module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFullProfileProduction
public import IntegerMultBounds.MathlibTM2.Routing.RouterProfileRank

/-! Every residue uses the same full matching table and the same production
budget. Coordinate casts change only types, not encoded input values. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

theorem matchingMateCoordinate_cast {M N : ℕ} (h : M = N) (mate : Fin N → Fin N) :
    matchingMateCoordinate (fun q : Fin M => Fin.cast h.symm (mate (Fin.cast h q))) =
      matchingMateCoordinate mate := by
  cases h
  rfl

theorem routerLocalSource_involutive (n K G : ℕ) (hn : K ≤ n) (r : Fin K)
    (mate : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hinv : Function.Involutive mate) :
    Function.Involutive (routerLocalSource n K G hn r mate) := by
  intro q
  simp only [routerLocalSource, Fin.cast_cast, Fin.cast_refl, id_eq]
  rw [hinv]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]

theorem routerLocalMatchingTargets (n K G : ℕ) (hn : K ≤ n) (r : Fin K)
    (mate : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hinv : Function.Involutive mate) (reverse : Bool) :
    matchingDirectionTargets (routerLocalSource n K G hn r mate) reverse =
      routerLocalTargets n K G hn r (matchingDirectionTargets mate reverse) := by
  ext q
  simp only [routerLocalTargets, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [matchingDirectionTargets_mem _ (routerLocalSource_involutive n K G hn r mate hinv),
    matchingDirectionTargets_mem mate hinv]
  rfl

theorem routerMatchingTable_common (n K G : ℕ) (hn : K ≤ n) (r : Fin K)
    (mate : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G)) :
    matchingTableEntries (routerProfileParameters n K G r.val).wy
        (matchingMateCoordinate (routerLocalSource n K G hn r mate)) =
      matchingTableEntries (routerTargetWidth n K G) (matchingMateCoordinate mate) := by
  rw [show matchingMateCoordinate (routerLocalSource n K G hn r mate) = matchingMateCoordinate mate from
    matchingMateCoordinate_cast (routerProfileParameters_width n K G hn r) mate,
    routerProfileParameters_width n K G hn r]

theorem routerMatchingProductionCost_common (n K G r Li Lk Lc : ℕ) :
    matchingFullProfileProductionCost (routerProfileParameters n K G r) (Li + Lk) Lk Lc =
      matchingFullProfileProductionCost (routerProfileParameters n K G 0) (Li + Lk) Lk Lc := by
  rfl

end
end IntegerMultBounds.MathlibTM2.Routing
