module

public import IntegerMultBounds.MathlibTM2.Routing.MiddleMatching
public import IntegerMultBounds.MathlibTM2.Routing.PlacementShear

/-! Three shears on the restricted middle field realize the full physical
matching, including every fixed surrounding coordinate and dirty borrowed bit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {N : ℕ} (B W : ℕ) (hfit : B + W ≤ N)
    (mate : Fin N → Fin N) (hinv : Function.Involutive mate)
    (hfix : ∀ q : Fin N, q.val < B ∨ B + W ≤ q.val → mate q = q)

def middleMatchingTargets : Finset (Fin N) :=
  (matchingLeft (middleMatching B W hfit mate hinv hfix)).image (middleCoordinate B W hfit)

theorem middleMatchingTargets_disjoint :
    Disjoint (middleMatchingTargets B W hfit mate hinv hfix)
      ((middleMatchingTargets B W hfit mate hinv hfix).image mate) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z, hz, hzq⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  have heq : middleMatching B W hfit mate hinv hfix r = q :=
    middleCoordinate_injective B W hfit ((middleMatching_coordinate B W hfit mate hinv hfix r).trans hzq)
  have hsource := matchingLeft_source (middleMatching B W hfit mate hinv hfix)
    (matchingLeft (middleMatching B W hfit mate hinv hfix))
    (matchingLeft_disjoint _ (middleMatching_involutive B W hfit mate hinv hfix)) r hr
  exact hsource (heq.symm ▸ hq)

theorem middleMatchingTargets_covers (q : Fin N)
    (hleft : q ∉ middleMatchingTargets B W hfit mate hinv hfix)
    (hright : q ∉ (middleMatchingTargets B W hfit mate hinv hfix).image mate) : mate q = q := by
  by_cases hmid : B ≤ q.val ∧ q.val < B + W
  · let q' : Fin W := ⟨q.val - B, by omega⟩
    have hq : middleCoordinate B W hfit q' = q := by
      apply Fin.ext
      change B + (q.val - B) = q.val
      omega
    have hl : q' ∉ matchingLeft (middleMatching B W hfit mate hinv hfix) := by
      intro hm
      exact hleft (Finset.mem_image.mpr ⟨q', hm, hq⟩)
    have hr : q' ∉ (matchingLeft (middleMatching B W hfit mate hinv hfix)).image
        (middleMatching B W hfit mate hinv hfix) := by
      intro hm
      obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hm
      apply hright
      refine Finset.mem_image.mpr ⟨middleCoordinate B W hfit r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
      rw [← middleMatching_coordinate B W hfit mate hinv hfix r, heq, hq]
    have hm := matchingLeft_covers _ (middleMatching_involutive B W hfit mate hinv hfix) q' hl hr
    rw [← hq, ← middleMatching_coordinate B W hfit mate hinv hfix q', hm]
  · exact hfix q (by omega)

theorem middleMatchingShears_eq (x : Fin N → Bool) :
    matchingShears mate (middleMatchingTargets B W hfit mate hinv hfix) x = fun q => x (mate q) :=
  matchingShears_eq mate hinv _ (middleMatchingTargets_disjoint B W hfit mate hinv hfix)
    (middleMatchingTargets_covers B W hfit mate hinv hfix) x

include hinv in
theorem placedMatching_involutive (e : Equiv.Perm (Fin N)) : Function.Involutive (placedSource e mate) := by
  intro q
  simp only [placedSource, e.apply_symm_apply]
  rw [hinv, e.symm_apply_apply]

omit hfix in
theorem placedMiddleMatchingShears_eq (e : Equiv.Perm (Fin N))
    (hfixed : ∀ q : Fin N, q.val < B ∨ B + W ≤ q.val → placedSource e mate q = q)
    (x : Fin N → Bool) :
    placeAddress e.symm
      (matchingShears (placedSource e mate)
        (middleMatchingTargets B W hfit (placedSource e mate) (placedMatching_involutive mate hinv e) hfixed)
        (placeAddress e x)) = fun q => x (mate q) := by
  rw [middleMatchingShears_eq]
  funext q
  simp only [placeAddress, placedSource, e.apply_symm_apply]

end IntegerMultBounds.MathlibTM2.Routing
