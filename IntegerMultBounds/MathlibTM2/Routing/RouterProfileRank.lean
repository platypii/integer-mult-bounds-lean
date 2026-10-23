module

public import IntegerMultBounds.MathlibTM2.Routing.RouterProfileSchedule

/-! A residue repair call on one common physical target field. Coordinate casts
change only types; source lookup and target membership use the shared geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits

theorem selectiveView_y_bit (p : Par) (X i : ℕ) (q : Fin p.wy) :
    (selectiveView p X i).y.testBit q.val = i.testBit (p.wc + q.val) := by
  change ((i / 2 ^ fieldOff (selectiveLen p X) 1) % 2 ^ p.wy).testBit q.val = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, selectiveFieldOff]
  simp [q.isLt, Nat.add_comm]

variable (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n) (r : Fin K)

def routerLocalTargets (targets : Finset (Fin (routerTargetWidth n K G))) :
    Finset (Fin (routerProfileParameters n K G r.val).wy) :=
  Finset.univ.filter fun q => Fin.cast (routerProfileParameters_width n K G hn r) q ∈ targets

def routerLocalSource (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (q : Fin (routerProfileParameters n K G r.val).wy) :
    Fin (routerProfileParameters n K G r.val).wy :=
  Fin.cast (routerProfileParameters_width n K G hn r).symm
    (source (Fin.cast (routerProfileParameters_width n K G hn r) q))

theorem routerLocalSource_allowed
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets) :
    ∀ q ∈ routerLocalTargets n K G hn r targets,
      routerLocalSource n K G hn r source q ∉ routerLocalTargets n K G hn r targets := by
  intro q hq hs
  simp only [routerLocalTargets, Finset.mem_filter, Finset.mem_univ, true_and] at hq hs
  simp only [routerLocalSource, Fin.cast_cast, Fin.cast_refl, id_eq] at hs
  exact hsource _ hq hs

def routerProfileRank (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G)) (i : ℕ) : ℕ :=
  let p := routerProfileParameters n K G r.val
  selectiveIdealIdx p X (profileActive p hK (routerLocalTargets n K G hn r targets))
    (profileSources p hK (routerLocalTargets n K G hn r targets)
      (routerLocalSource n K G hn r source)) i

/-- Every residue call has the scheduler's exact shear action in shared physical
coordinates; the borrowed-field offset is independent of the residue. -/
theorem routerProfileRank_bits (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G)) (i : ℕ) :
    (fun q : Fin (routerTargetWidth n K G) =>
      (routerProfileRank n K G hK hn r X targets source i).testBit
        (routerBorrowed n K G + q.val)) =
      shear ((routerBulkTargets n K G targets).filter fun q => q.val % K = r.val) source
        (fun q => i.testBit (routerBorrowed n K G + q.val)) := by
  funext q
  let p := routerProfileParameters n K G r.val
  let q' : Fin p.wy := Fin.cast (routerProfileParameters_width n K G hn r).symm q
  have h := congrFun (profileIdeal_shear p hK X (routerLocalTargets n K G hn r targets)
    (routerLocalSource n K G hn r source) i) q'
  rw [routerProfilePassTargets n K G hK hn r] at h
  dsimp only [p, q'] at h
  simp only [shear, toggle, Finset.mem_filter, routerLocalTargets, Finset.mem_univ,
    true_and, routerLocalSource, Fin.cast_cast, Fin.cast_refl, id_eq,
    selectiveView_y_bit, routerProfileParameters_borrowed] at h
  simpa only [routerProfileRank, routerLocalTargets, p, q', Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq,
    shear, toggle, routerBulkTargets, Finset.mem_filter, and_assoc] using h

/-- Each rank call restores every borrowed and spectator bit. -/
theorem routerProfileRank_outside (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (i q : ℕ)
    (hq : q < routerBorrowed n K G ∨ routerBorrowed n K G + routerTargetWidth n K G ≤ q) :
    (routerProfileRank n K G hK hn r X targets source i).testBit q = i.testBit q := by
  unfold routerProfileRank
  rw [selectiveIdealIdx_bit]
  simp only [routerProfileParameters_borrowed, routerProfileParameters_width n K G hn r]
  rw [ite_eq_right (by omega)]

/-- Rank composition follows the same inside-to-outside order as partitionShears. -/
def routerProfileRanks (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G)) :
    List (Fin K) → ℕ → ℕ
  | [], i => i
  | r :: rs, i => routerProfileRank n K G hK hn r X targets source
      (routerProfileRanks X targets source rs i)

theorem routerProfileRanks_bits (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (rs : List (Fin K)) (i : ℕ) :
    (fun q : Fin (routerTargetWidth n K G) =>
      (routerProfileRanks n K G hK hn X targets source rs i).testBit
        (routerBorrowed n K G + q.val)) =
      partitionShears (routerBulkTargets n K G targets) source
        (fun q => (⟨q.val % K, Nat.mod_lt _ hK⟩ : Fin K)) rs
        (fun q => i.testBit (routerBorrowed n K G + q.val)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [routerProfileRanks, routerProfileRank_bits, ih]
    change shear _ source _ = shear _ source _
    congr 1
    ext q
    simp only [Finset.mem_filter, Fin.ext_iff]

theorem routerProfileRanks_outside (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (rs : List (Fin K)) (i q : ℕ)
    (hq : q < routerBorrowed n K G ∨ routerBorrowed n K G + routerTargetWidth n K G ≤ q) :
    (routerProfileRanks n K G hK hn X targets source rs i).testBit q = i.testBit q := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [routerProfileRanks, routerProfileRank_outside n K G hK hn r X targets source _ q hq, ih]

theorem routerProfileRanks_row (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (rs : List (Fin K)) (i : ℕ) :
    routerProfileRanks n K G hK hn X targets source rs i /
        2 ^ (routerBorrowed n K G + routerTargetWidth n K G) =
      i / 2 ^ (routerBorrowed n K G + routerTargetWidth n K G) := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [Nat.testBit_div_two_pow]
  exact routerProfileRanks_outside n K G hK hn X targets source rs i _ (Or.inr (by omega))

/-- All bulk rank calls together realize exactly the requested bulk shear. -/
theorem routerProfileRanks_bulk (X : ℕ)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (source : Fin (routerTargetWidth n K G) → Fin (routerTargetWidth n K G))
    (hsource : ∀ q ∈ targets, source q ∉ targets) (i : ℕ) :
    (fun q : Fin (routerTargetWidth n K G) =>
      (routerProfileRanks n K G hK hn X targets source (List.finRange K) i).testBit
        (routerBorrowed n K G + q.val)) =
      shear (routerBulkTargets n K G targets) source
        (fun q => i.testBit (routerBorrowed n K G + q.val)) := by
  have hb : ∀ q ∈ routerBulkTargets n K G targets,
      source q ∉ routerBulkTargets n K G targets := by
    intro q hq hs
    exact hsource q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hs).1
  rw [routerProfileRanks_bits, residueShears_eq _ _ hb K hK]

end IntegerMultBounds.MathlibTM2.Routing
