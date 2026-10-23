module

public import IntegerMultBounds.MathlibTM2.Routing.Shear
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Union

/-!
# Partition a directional shear without changing its sources

The source condition is imposed on the complete target set. Consequently every
partial pass preserves all sources, and partition order is immaterial. The final
residue class includes terminal coordinates; a later physical compiler must split
those off rather than silently discard them.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem shear_union (a b : Finset ι) (source : ι → ι)
    (separate : Disjoint a b)
    (hsource : ∀ i ∈ a ∪ b, source i ∉ a ∪ b) (x : ι → Bool) :
    shear a source (shear b source x) = shear (a ∪ b) source x := by
  funext i
  by_cases ha : i ∈ a
  · have hb : i ∉ b := fun h => Finset.disjoint_left.mp separate ha h
    have hs := hsource i (Finset.mem_union_left b ha)
    simp only [Finset.mem_union, not_or] at hs
    simp [shear, toggle, ha, hb, hs.2]
  · by_cases hb : i ∈ b
    · simp [shear, toggle, ha, hb]
    · simp [shear, toggle, ha, hb]

def partitionShears (targets : Finset ι) (source : ι → ι) (color : ι → κ) :
    List κ → (ι → Bool) → (ι → Bool)
  | [], x => x
  | k :: ks, x => shear (targets.filter fun i => color i = k) source
      (partitionShears targets source color ks x)

theorem partitionShears_eq (targets : Finset ι) (source : ι → ι) (color : ι → κ)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (ks : List κ) (hn : ks.Nodup)
    (x : ι → Bool) :
    partitionShears targets source color ks x =
      shear (targets.filter fun i => color i ∈ ks) source x := by
  induction ks with
  | nil =>
    simp [partitionShears, shear]
    funext i
    simp [toggle]
  | cons k ks ih =>
    obtain ⟨hk, hn⟩ := List.nodup_cons.mp hn
    rw [partitionShears, ih hn]
    have hd : Disjoint (targets.filter fun i => color i = k)
        (targets.filter fun i => color i ∈ ks) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      exact hk (hi' ▸ hj')
    have hs : ∀ i ∈ (targets.filter fun i => color i = k) ∪
        (targets.filter fun i => color i ∈ ks),
        source i ∉ (targets.filter fun i => color i = k) ∪
          (targets.filter fun i => color i ∈ ks) := by
      intro i hi hj
      have sub : (targets.filter fun i => color i = k) ∪
          (targets.filter fun i => color i ∈ ks) ⊆ targets := by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact (Finset.mem_filter.mp hj).1
        · exact (Finset.mem_filter.mp hj).1
      exact hsource i (sub hi) (sub hj)
    rw [shear_union _ _ source hd hs]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, List.mem_cons]
    tauto

/-- Splitting by all residues performs the complete directional shear. -/
theorem residueShears_eq (targets : Finset (Fin n)) (source : Fin n → Fin n)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (K : ℕ) (hK : 0 < K)
    (x : Fin n → Bool) :
    partitionShears targets source (fun i => (⟨i.val % K, Nat.mod_lt _ hK⟩ : Fin K))
      (List.finRange K) x = shear targets source x := by
  rw [partitionShears_eq _ _ _ hsource _ (List.nodup_finRange K)]
  congr 1
  ext i
  simp


/-- Partition shears after an injective physical embedding. The traversal is
still the existing partition shear; only its coordinate representation changes. -/
theorem partitionShears_image {δ : Type*} [DecidableEq δ]
    (targets : Finset ι) (f : ι → δ) (hf : Function.Injective f)
    (source : δ → δ) (color : ι → κ) (defaultColor : κ)
    (hsource : ∀ i ∈ targets.image f, source i ∉ targets.image f)
    (ks : List κ) (hn : ks.Nodup) (x : δ → Bool) :
    ks.foldr (fun k y => shear ((targets.filter fun i => color i = k).image f) source y) x =
      shear ((targets.filter fun i => color i ∈ ks).image f) source x := by
  classical
  let physicalColor := Function.extend f color (fun _ => defaultColor)
  have hcolor (i : ι) : physicalColor (f i) = color i := hf.extend_apply _ _ i
  have hfilter (k : κ) :
      (targets.image f).filter (fun i => physicalColor i = k) =
        (targets.filter fun i => color i = k).image f := by
    rw [Finset.filter_image]
    simp only [hcolor]
  have hfold : ∀ stages : List κ,
      stages.foldr (fun k y => shear ((targets.filter fun i => color i = k).image f) source y) x =
        partitionShears (targets.image f) source physicalColor stages x := by
    intro stages
    induction stages with
    | nil => rfl
    | cons k stages ih =>
      simp only [List.foldr_cons, partitionShears, hfilter, ih]
  rw [hfold, partitionShears_eq _ _ _ hsource ks hn, Finset.filter_image]
  simp only [hcolor]

end IntegerMultBounds.MathlibTM2.Routing
