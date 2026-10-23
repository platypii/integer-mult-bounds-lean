module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingShears
public import Mathlib.Data.Finset.Image

/-!
# Transport a shear through coordinate placement and its inverse

Placement changes source names as well as target names. These identities ensure
that displaced live coordinates are read at their actual positions, and that
undoing the placement restores every borrowed reservoir coordinate.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι]

def placeAddress (e : Equiv.Perm ι) (x : ι → Bool) : ι → Bool := fun i => x (e i)

def placedTargets (e : Equiv.Perm ι) (targets : Finset ι) : Finset ι :=
  targets.image e.symm

def placedSource (e : Equiv.Perm ι) (source : ι → ι) : ι → ι :=
  fun i => e.symm (source (e i))

@[simp] theorem mem_placedTargets (e : Equiv.Perm ι) (targets : Finset ι) (i : ι) :
    i ∈ placedTargets e targets ↔ e i ∈ targets := by
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    simpa [← he] using hj
  · intro hi
    exact Finset.mem_image.mpr ⟨e i, hi, e.symm_apply_apply i⟩

theorem placedSource_allowed (e : Equiv.Perm ι) (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) :
    ∀ i ∈ placedTargets e targets, placedSource e source i ∉ placedTargets e targets := by
  intro i hi hj
  have hi' := (mem_placedTargets e targets i).mp hi
  have hj' := (mem_placedTargets e targets _).mp hj
  simp only [placedSource, e.apply_symm_apply] at hj'
  exact hsource _ hi' hj'

theorem placedShear_eq (e : Equiv.Perm ι) (targets : Finset ι) (source : ι → ι)
    (x : ι → Bool) :
    shear (placedTargets e targets) (placedSource e source) (placeAddress e x) =
      placeAddress e (shear targets source x) := by
  funext i
  simp [shear, toggle, placeAddress, placedSource]

/-- Placing, running the renamed shear and unplacing gives the original shear. -/
theorem unplace_placedShear (e : Equiv.Perm ι) (targets : Finset ι) (source : ι → ι)
    (x : ι → Bool) :
    placeAddress e.symm
      (shear (placedTargets e targets) (placedSource e source) (placeAddress e x)) =
        shear targets source x := by
  rw [placedShear_eq]
  funext i
  simp [placeAddress]

/-- Arbitrary reservoir bits survive placement and undoing; no zero assumption. -/
theorem unplace_placedShear_reservoir (e : Equiv.Perm ι) (targets bank : Finset ι)
    (source : ι → ι) (separate : Disjoint targets bank) (x : ι → Bool)
    (i : ι) (hi : i ∈ bank) :
    placeAddress e.symm
      (shear (placedTargets e targets) (placedSource e source) (placeAddress e x)) i = x i := by
  rw [unplace_placedShear]
  have ht : i ∉ targets := fun h => Finset.disjoint_left.mp separate h hi
  simp [shear, toggle, ht]

omit [DecidableEq ι] in
/-- Conjugating a matching preserves its involution property. -/
theorem placedSource_involutive (e : Equiv.Perm ι) (mate : ι → ι)
    (hinv : Function.Involutive mate) : Function.Involutive (placedSource e mate) := by
  intro i
  simp only [placedSource, e.apply_symm_apply]
  rw [hinv, e.symm_apply_apply]

omit [DecidableEq ι] in
/-- Fixed reservoir coordinates remain fixed at their placed physical positions. -/
theorem placedSource_fixes (e : Equiv.Perm ι) (mate : ι → ι) (bank : Finset ι)
    (hfix : ∀ i ∈ bank, mate i = i) (i : ι) (hi : e i ∈ bank) :
    placedSource e mate i = i := by
  simp only [placedSource, hfix _ hi, e.symm_apply_apply]

omit [DecidableEq ι] in
/-- A live matching source cannot enter the placed reservoir either. -/
theorem placedSource_avoids (e : Equiv.Perm ι) (mate : ι → ι) (bank : Finset ι)
    (hinv : Function.Involutive mate) (hfix : ∀ i ∈ bank, mate i = i)
    (i : ι) (hi : e i ∉ bank) : e (placedSource e mate i) ∉ bank := by
  simp only [placedSource, e.apply_symm_apply]
  intro hm
  have he := hfix _ hm
  rw [hinv] at he
  exact hi (he ▸ hm)


/-- The complete three-shear matching schedule transports through placement,
including its orientation, without imposing physical endpoint order. -/
theorem placedMatchingShears_eq (e : Equiv.Perm ι) (mate : ι → ι) (left : Finset ι)
    (x : ι → Bool) :
    matchingShears (placedSource e mate) (placedTargets e left) (placeAddress e x) =
      placeAddress e (matchingShears mate left x) := by
  have hright : (placedTargets e left).image (placedSource e mate) =
      placedTargets e (left.image mate) := by
    simp only [placedTargets, Finset.image_image]
    congr 1
    funext i
    simp only [Function.comp_apply, placedSource, e.apply_symm_apply]
  simp only [matchingShears, hright, placedShear_eq]

end IntegerMultBounds.MathlibTM2.Routing
