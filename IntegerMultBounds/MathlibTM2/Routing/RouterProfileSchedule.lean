module

public import IntegerMultBounds.MathlibTM2.Routing.RouterTerminal
public import IntegerMultBounds.MathlibTM2.Routing.TerminalShears
public import IntegerMultBounds.MathlibTM2.Routing.ProfileIdealShear

/-! Bulk and terminal shears in the router's common-width reservoir geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def routerBulkTargets (n K G : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G))) :=
  targets.filter fun i => i.val < routerDigits n K G * K

/-- A residue profile enumerates exactly its bulk targets, without padding calls. -/
theorem routerProfileTarget_iff (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n)
    (r : Fin K) (i : Fin (routerTargetWidth n K G)) :
    (∃ c, Fin.cast (routerProfileParameters_width n K G hn r)
      (profileTarget (routerProfileParameters n K G r.val) hK c) = i) ↔
      i.val < routerDigits n K G * K ∧ i.val % K = r.val := by
  constructor
  · rintro ⟨c, hc⟩
    have hv := congrArg Fin.val hc
    change r.val + c.val * K = i.val at hv
    refine ⟨?_, ?_⟩
    · have hb := routerProfile_target_bulk n K G hK r c
      change r.val + c.val * K < routerDigits n K G * K at hb
      omega
    · rw [← hv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
  · rintro ⟨hi, hr⟩
    have hc := (Nat.div_lt_iff_lt_mul hK).mpr hi
    refine ⟨⟨i.val / K, hc⟩, ?_⟩
    apply Fin.ext
    change r.val + i.val / K * K = i.val
    have he := Nat.mod_add_div i.val K
    nlinarith

/-- The exact repair profile selects precisely one scheduler residue class. -/
theorem routerProfilePassTargets (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n)
    (r : Fin K)
    (targets : Finset (Fin (routerProfileParameters n K G r.val).wy)) :
    profilePassTargets (routerProfileParameters n K G r.val) hK targets =
      targets.filter (fun q => q.val < routerDigits n K G * K ∧ q.val % K = r.val) := by
  ext q
  simp only [profilePassTargets, Finset.mem_filter]
  apply and_congr_right
  intro _
  have h := routerProfileTarget_iff n K G hK hn r
    (Fin.cast (routerProfileParameters_width n K G hn r) q)
  simpa only [Fin.cast_inj, Fin.val_cast] using h

/-- Fixed-count bulk profiles and the complete elementary suffix realize one shear. -/
theorem router_bulk_terminal_shears_eq (n K G : ℕ) (hK : 0 < K)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ i ∈ targets, source i ∉ targets)
    (x : Fin (routerTargetWidth n K G) → Bool) :
    partitionShears (routerBulkTargets n K G targets) source
      (fun i => (⟨i.val % K, Nat.mod_lt _ hK⟩ : Fin K)) (List.finRange K)
      (elementaryShears source (routerTerminalTargets n K G targets).toList x) =
      shear targets source x := by
  have hs (a : Finset (Fin (routerTargetWidth n K G))) (ha : a ⊆ targets) :
      ∀ i ∈ a, source i ∉ a := fun i hi hj => hsource i (ha hi) (ha hj)
  have hb : ∀ i ∈ routerBulkTargets n K G targets,
      source i ∉ routerBulkTargets n K G targets := hs _ (Finset.filter_subset _ _)
  have ht : ∀ i ∈ routerTerminalTargets n K G targets,
      source i ∉ routerTerminalTargets n K G targets := hs _ (Finset.filter_subset _ _)
  rw [residueShears_eq _ _ hb K hK, elementaryShears_eq _ _ ht]
  have hu : routerBulkTargets n K G targets ∪ routerTerminalTargets n K G targets = targets := by
    ext i
    simp only [routerBulkTargets, routerTerminalTargets, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hi | hi) <;> exact hi.1
    · intro hi
      by_cases hb : i.val < routerDigits n K G * K
      · exact Or.inl ⟨hi, hb⟩
      · exact Or.inr ⟨hi, Nat.le_of_not_gt hb⟩
  have hd : Disjoint (routerBulkTargets n K G targets) (routerTerminalTargets n K G targets) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_filter.mp hj).2) (Finset.mem_filter.mp hi).2
  have hboth : ∀ i ∈ routerBulkTargets n K G targets ∪ routerTerminalTargets n K G targets,
      source i ∉ routerBulkTargets n K G targets ∪ routerTerminalTargets n K G targets := by
    simpa only [hu] using hsource
  rw [shear_union _ _ source hd hboth, hu]

end IntegerMultBounds.MathlibTM2.Routing
