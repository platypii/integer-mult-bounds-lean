module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileCompiler
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdealBits
public import IntegerMultBounds.MathlibTM2.Routing.Shear

/-! Identify exact R2's physical target-field action with one logical profile shear. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits

def profilePassTargets (p : Par) (hK : 0 < p.K) (targets : Finset (Fin p.wy)) :
    Finset (Fin p.wy) :=
  targets.filter fun q => ∃ c, profileTarget p hK c = q

/-- The exact destination map performs the scheduler's shear on every address,
including exceptional addresses, without assuming the borrowed fields are zero. -/
theorem profileIdeal_shear (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (i : ℕ) :
    (fun q : Fin p.wy =>
      (selectiveView p X (selectiveIdealIdx p X (profileActive p hK targets)
        (profileSources (X := X) p hK targets source) i)).y.testBit q.val) =
      shear (profilePassTargets p hK targets) source
        (fun q => (selectiveView p X i).y.testBit q.val) := by
  funext q
  rw [selectiveIdeal_view hK]
  change ((selectiveView p X i).y ^^^
    targetWord p (profileActive p hK targets) (profileSources (X := X) p hK targets source)
      (selectiveView p X i).y (selectiveView p X i).x).testBit q.val = _
  rw [Nat.testBit_xor]
  by_cases hslot : ∃ c, profileTarget p hK c = q
  · obtain ⟨c, hc⟩ := hslot
    have hpos : posS p c.val = q.val := congrArg Fin.val hc
    rw [← hpos, targetWord_bit hK]
    by_cases ht : q ∈ targets
    · have ha : profileActive p hK targets c = true := by
        simp only [profileActive, hc, ht, decide_true]
      rw [ha, Bool.true_and, profileSources_physical p hK targets source c ha]
      simp only [hc]
      have hpass : q ∈ profilePassTargets p hK targets :=
        Finset.mem_filter.mpr ⟨ht, ⟨c, hc⟩⟩
      simp only [shear, toggle, hpass, ite_true]
      rw [hpos]
    · have ha : profileActive p hK targets c = false := by
        simp only [profileActive, hc, ht, decide_false]
      have hpass : q ∉ profilePassTargets p hK targets :=
        fun h => ht (Finset.mem_filter.mp h).1
      simp only [ha, Bool.false_and, Bool.xor_false, shear, toggle, hpass, ite_false]
      rw [hpos]
  · have hzero : (targetWord p (profileActive p hK targets)
        (profileSources (X := X) p hK targets source) (selectiveView p X i).y
        (selectiveView p X i).x).testBit q.val = false := by
      apply targetWord_other_bit hK
      intro c _ he
      exact hslot ⟨c, Fin.ext he.symm⟩
    have hpass : q ∉ profilePassTargets p hK targets :=
      fun h => hslot (Finset.mem_filter.mp h).2
    simp only [hzero, Bool.xor_false, shear, toggle, hpass, ite_false]

/-- The actual finite rank permutation returned by executed exact repair has the
same shear contract; the source-preservation premise supplies its bijectivity. -/
theorem profileIdealPerm_shear (p : Par) (hK : 0 < p.K) (X R : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (fun q : Fin p.wy =>
      (selectiveView p X ((selectiveIdealPerm hK (profileActive p hK targets)
        (profileSources (X := X) p hK targets source) R
        (profileSources_allowed p hK targets source hsource)) i).val).y.testBit q.val) =
      shear (profilePassTargets p hK targets) source
        (fun q => (selectiveView p X i.val).y.testBit q.val) :=
  profileIdeal_shear p hK X targets source i.val

end IntegerMultBounds.MathlibTM2.Routing
