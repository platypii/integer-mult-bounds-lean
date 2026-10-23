module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingShears
public import IntegerMultBounds.MathlibTM2.Routing.ProfileCoordinateGenerate

/-! Matching directions determine each physical source and activity by one comparison.
This is the specification for producing profile input from matching entries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

/-- False targets the smaller endpoint; true targets the larger endpoint. -/
def matchingCoordinateEnabled (reverse : Bool) (q mate : ℕ) : Bool :=
  if reverse then decide (mate < q) else decide (q < mate)

def matchingCoordinateInput (reverse : Bool) (q mate : ℕ) : ℕ × Bool :=
  let enabled := matchingCoordinateEnabled reverse q mate
  (if enabled then mate else q, enabled)

def matchingDirectionTargets {N : ℕ} (mate : Fin N → Fin N) (reverse : Bool) : Finset (Fin N) :=
  if reverse then (matchingLeft mate).image mate else matchingLeft mate

theorem matchingDirectionTargets_mem {N : ℕ} (mate : Fin N → Fin N)
    (hinv : Function.Involutive mate) (reverse : Bool) (q : Fin N) :
    q ∈ matchingDirectionTargets mate reverse ↔ matchingCoordinateEnabled reverse q.val (mate q).val = true := by
  cases reverse
  · simp only [matchingDirectionTargets, matchingCoordinateEnabled, matchingLeft,
      Bool.false_eq_true, ite_false, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    rfl
  · rw [matchingDirectionTargets, ite_eq_left rfl, matchingRight_mem mate hinv]
    simp only [matchingLeft, matchingCoordinateEnabled, ite_true, Finset.mem_filter,
      Finset.mem_univ, true_and, hinv q, decide_eq_true_eq]
    rfl

theorem matchingDirectionTargets_source {N : ℕ} (mate : Fin N → Fin N)
    (hinv : Function.Involutive mate) (reverse : Bool) :
    ∀ q ∈ matchingDirectionTargets mate reverse, mate q ∉ matchingDirectionTargets mate reverse := by
  cases reverse
  · exact matchingLeft_source mate (matchingLeft mate) (matchingLeft_disjoint mate hinv)
  · exact matchingRight_source mate hinv (matchingLeft mate) (matchingLeft_disjoint mate hinv)

/-- Inactive slots read themselves; fixed points are inactive in both directions. -/
theorem matchingCoordinateInput_fixed (reverse : Bool) (q : ℕ) :
    matchingCoordinateInput reverse q q = (q, false) := by
  cases reverse <;> simp [matchingCoordinateInput, matchingCoordinateEnabled]

theorem profileCoordinateInputs_matching (p : Par) (hK : 0 < p.K)
    (mate : Fin p.wy → Fin p.wy) (hinv : Function.Involutive mate) (reverse : Bool) :
    profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate =
      List.ofFn (fun c : Fin p.n => matchingCoordinateInput reverse
        (profileTarget p hK c).val (mate (profileTarget p hK c)).val) := by
  unfold profileCoordinateInputs
  apply congrArg List.ofFn
  funext c
  have hactive : profileActive p hK (matchingDirectionTargets mate reverse) c =
      matchingCoordinateEnabled reverse (profileTarget p hK c).val (mate (profileTarget p hK c)).val := by
    apply Bool.eq_iff_iff.mpr
    simpa only [profileActive, decide_eq_true_eq] using
      matchingDirectionTargets_mem mate hinv reverse (profileTarget p hK c)
  unfold matchingCoordinateInput profileSourceCoordinate
  rw [← hactive]
  simp only [profileActive]
  split_ifs <;> simp_all

/-- The input producer needs only bounded matching entries, never decoded R2 records. -/
theorem matchingCoordinateInput_bound (reverse : Bool) (q mate W : ℕ)
    (hq : q < W) (hmate : mate < W) : (matchingCoordinateInput reverse q mate).1 < W := by
  dsimp only [matchingCoordinateInput]
  split_ifs <;> assumption

end
end IntegerMultBounds.MathlibTM2.Routing
