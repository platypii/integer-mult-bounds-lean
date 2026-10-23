module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedSelectiveShear
public import IntegerMultBounds.MathlibTM2.Routing.ProfileSourceRecords
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassLocalTable
public import IntegerMultBounds.MathlibTM2.Routing.RouterProfileRank

/-! Interpret compiled profile permutations as physical matching shears. The
source intertwining equation is explicit, so placement geometry cannot silently
differ from the geometry used to generate the local matching table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def profileMiddleCoordinate (p : Par) (X : ℕ) : Fin p.wy → Fin (fieldsLen (selectiveLen p X)) :=
  middleCoordinate p.wc p.wy (by rw [selectiveFieldsLen]; omega)

theorem selectiveTargetPosition_profileMiddle (p : Par) (X : ℕ) (hK : 0 < p.K) (c : Fin p.n) :
    selectiveTargetPosition p X hK c = profileMiddleCoordinate p X (profileTarget p hK c) := by
  apply Fin.ext
  rfl

theorem selectiveSourcePosition_profileMiddle (p : Par) (X : ℕ) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (c : Fin p.n) :
    selectiveSourcePosition p X (profileSources p hK targets source c) =
      profileMiddleCoordinate p X (profileSourceCoordinate p hK targets source c) := by
  apply Fin.ext
  change p.wc + (sourceWire p X (sourceOfY p hK _)).val = p.wc + _
  rw [sourceOfY_wire]

theorem placedProfileTargets_image (p : Par) (X : ℕ) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X)))) :
    placedSelectiveTargets p X hK (profileActive p hK targets) e =
      (profilePassTargets p hK targets).image (fun q => e (profileMiddleCoordinate p X q)) := by
  ext q
  rw [mem_placedSelectiveTargets]
  constructor
  · rintro ⟨c, hc, he⟩
    have ht : profileTarget p hK c ∈ targets := by simpa only [profileActive, decide_eq_true_eq] using hc
    apply Finset.mem_image.mpr
    refine ⟨profileTarget p hK c, Finset.mem_filter.mpr ⟨ht, ⟨c, rfl⟩⟩, ?_⟩
    rwa [selectiveTargetPosition_profileMiddle] at he
  · intro hq
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hq
    obtain ⟨ht, c, hc⟩ := Finset.mem_filter.mp hr
    subst r
    exact ⟨c, by simpa only [profileActive, decide_eq_true_eq] using ht,
      by rwa [selectiveTargetPosition_profileMiddle]⟩

/-- For the actual router parameters the selected physical coordinates are
exactly the chosen residue in the bulk, transported through placement. -/
theorem routerPlacedProfileTargets (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n) (r : Fin K)
    (X : ℕ) (targets : Finset (Fin (routerProfileParameters n K G r.val).wy))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen (routerProfileParameters n K G r.val) X)))) :
    placedSelectiveTargets (routerProfileParameters n K G r.val) X hK
        (profileActive (routerProfileParameters n K G r.val) hK targets) e =
      (targets.filter fun q => q.val < routerDigits n K G * K ∧ q.val % K = r.val).image
        (fun q => e (profileMiddleCoordinate (routerProfileParameters n K G r.val) X q)) := by
  exact (placedProfileTargets_image (routerProfileParameters n K G r.val) X hK targets e).trans
    (congrArg (fun ts => ts.image (fun q => e (profileMiddleCoordinate (routerProfileParameters n K G r.val) X q)))
      (routerProfilePassTargets n K G hK hn r targets))

/-- A placed actual router profile selects the placed image of one bulk
residue in the common middle-coordinate type. -/
theorem routerPlacedLocalTargets (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n) (r : Fin K)
    (targets : Finset (Fin (routerTargetWidth n K G)))
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen (routerProfileParameters n K G r.val) 0)))) :
    placedSelectiveTargets (routerProfileParameters n K G r.val) 0 hK
      (profileActive (routerProfileParameters n K G r.val) hK (routerLocalTargets n K G hn r targets)) e =
      ((routerBulkTargets n K G targets).filter (fun q => q.val % K = r.val)).image
        (fun q => e (profileMiddleCoordinate (routerProfileParameters n K G r.val) 0
          (Fin.cast (routerProfileParameters_width n K G hn r).symm q))) := by
  rw [placedProfileTargets_image (routerProfileParameters n K G r.val) 0 hK
    (routerLocalTargets n K G hn r targets) e, ← routerLocalPassTargets_image n K G hK hn r targets,
    Finset.image_image]
  congr 1

theorem routerProfileFieldsLen (n K G : ℕ) (hn : K ≤ n) (r : Fin K) :
    fieldsLen (selectiveLen (routerProfileParameters n K G r.val) 0) = n := by
  have ht := routerProfileParameters_total n K G hn r
  rw [selectiveFieldsLen]
  omega

theorem profilePlacedSource_mate (p : Par) (X : ℕ) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (mate : Fin (fieldsLen (selectiveLen p X)) → Fin (fieldsLen (selectiveLen p X)))
    (hsource : ∀ q, e (profileMiddleCoordinate p X (source q)) = mate (e (profileMiddleCoordinate p X q)))
    (c : Fin p.n) (hc : profileActive p hK targets c = true) :
    e (selectiveSourcePosition p X (profileSources p hK targets source c)) =
      mate (e (selectiveTargetPosition p X hK c)) := by
  have ht : profileTarget p hK c ∈ targets := by simpa only [profileActive, decide_eq_true_eq] using hc
  rw [selectiveSourcePosition_profileMiddle, selectiveTargetPosition_profileMiddle]
  simp only [profileSourceCoordinate, ite_eq_left ht]
  exact hsource _

/-- An actual placed profile permutation reads the original physical mate at
every selected target and fixes every other bit. -/
theorem profilePlacedPerm_matching_shear {p : Par} {X R : ℕ} (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hallowed : ∀ q ∈ targets, source q ∉ targets)
    (e : Equiv.Perm (Fin (fieldsLen (selectiveLen p X))))
    (f : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))))
    (hf : ∀ i q, (f i).val.testBit q.val = i.val.testBit (e q).val)
    (mate : Fin (fieldsLen (selectiveLen p X)) → Fin (fieldsLen (selectiveLen p X)))
    (hsource : ∀ q, e (profileMiddleCoordinate p X (source q)) = mate (e (profileMiddleCoordinate p X q)))
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (fun q => (placedSelectivePerm hK (profileActive p hK targets) (profileSources p hK targets source)
      (profileSources_allowed p hK targets source hallowed) f i).val.testBit q.val) =
      shear (placedSelectiveTargets p X hK (profileActive p hK targets) e) mate (fun q => i.val.testBit q.val) := by
  rw [placedSelectivePerm_shear hK _ _ _ e f hf]
  funext q
  by_cases hq : q ∈ placedSelectiveTargets p X hK (profileActive p hK targets) e
  · obtain ⟨c, hc, rfl⟩ := (mem_placedSelectiveTargets hK (profileActive p hK targets) e q).mp hq
    rw [shear, shear, toggle, toggle, ite_eq_left hq, ite_eq_left hq, placedSelectiveSource_at,
      profilePlacedSource_mate p X hK targets source e mate hsource c hc]
  · simp only [shear, toggle, ite_eq_right hq]


/-- Physical middle placement is independent of the profile's width casts. -/
theorem profileMiddlePlacement_cast (p : Par) (n H : ℕ)
    (hrecord : fieldsLen (selectiveLen p 0) = n)
    (hwidth : p.wy = n - 3 * p.wc)
    (hfit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (k : Fin 3)
    (q : Fin (n - 3 * p.wc)) :
    Fin.cast hrecord (reservoirPlacement (fieldsLen (selectiveLen p 0)) H hfit p.wc hw k
      (profileMiddleCoordinate p 0 (Fin.cast hwidth.symm q))) =
    reservoirPlacement n H (hrecord ▸ hfit) p.wc hw k
      (middleCoordinate p.wc (n - 3 * p.wc)
        (reservoirMiddle_fit n H (hrecord ▸ hfit) p.wc hw) q) := by
  subst n
  apply congrArg (reservoirPlacement (fieldsLen (selectiveLen p 0)) H hfit p.wc hw k)
  apply Fin.ext
  rfl

/-- Placed residue targets share one physical embedding across all residues. -/
theorem routerPlacedLocalTargets_cast (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n) (r : Fin K)
    (targets : Finset (Fin (routerTargetWidth n K G))) (H : ℕ)
    (hfit : 9 * H ≤ fieldsLen (selectiveLen (routerProfileParameters n K G r.val) 0))
    (hw : routerBorrowed n K G ≤ H) (k : Fin 3) :
    (placedSelectiveTargets (routerProfileParameters n K G r.val) 0 hK
      (profileActive (routerProfileParameters n K G r.val) hK (routerLocalTargets n K G hn r targets))
      (reservoirPlacement (fieldsLen (selectiveLen (routerProfileParameters n K G r.val) 0)) H hfit
        (routerBorrowed n K G) hw k)).image (Fin.cast (routerProfileFieldsLen n K G hn r)) =
    ((routerBulkTargets n K G targets).filter (fun q => q.val % K = r.val)).image
      (fun q => reservoirPlacement n H ((routerProfileFieldsLen n K G hn r) ▸ hfit)
        (routerBorrowed n K G) hw k
        (middleCoordinate (routerBorrowed n K G) (routerTargetWidth n K G)
          (reservoirMiddle_fit n H ((routerProfileFieldsLen n K G hn r) ▸ hfit)
            (routerBorrowed n K G) hw) q)) := by
  rw [routerPlacedLocalTargets n K G hK hn r targets, Finset.image_image]
  congr 1
  funext q
  exact profileMiddlePlacement_cast (routerProfileParameters n K G r.val) n H
    (routerProfileFieldsLen n K G hn r) (routerProfileParameters_width n K G hn r) hfit hw k q

/-- With no appended spectator field, the compiler's Y field is exactly the
middle interval used by the executed original-matching table producer. -/
theorem profileMiddleWidth (p : Par) : p.wy = fieldsLen (selectiveLen p 0) - 3 * p.wc := by
  rw [selectiveFieldsLen]
  omega

theorem reservoirProfileClassSource_coordinate (p : Par) (X : ℕ)
    (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p X)) (hw : p.wc ≤ H) (k : Fin 3)
    (mate : Fin (fieldsLen (selectiveLen p X)) → Fin (fieldsLen (selectiveLen p X)))
    (hinv : Function.Involutive mate) (hwidth : p.wy = fieldsLen (selectiveLen p X) - 3 * p.wc) (q : Fin p.wy) :
    let e := reservoirPlacement (fieldsLen (selectiveLen p X)) H hfit p.wc hw k
    let source := fun q : Fin p.wy => Fin.cast hwidth.symm
      (reservoirClassLocalMatching (fieldsLen (selectiveLen p X)) H hfit p.wc hw k mate hinv (Fin.cast hwidth q))
    e (profileMiddleCoordinate p X (source q)) =
      matchingClass (routingReservoir (fieldsLen (selectiveLen p X)) H hfit) mate k (e (profileMiddleCoordinate p X q)) := by
  dsimp only
  have hmid (q : Fin p.wy) : profileMiddleCoordinate p X q =
      middleCoordinate p.wc (fieldsLen (selectiveLen p X) - 3 * p.wc)
        (reservoirMiddle_fit (fieldsLen (selectiveLen p X)) H hfit p.wc hw) (Fin.cast hwidth q) := by
    apply Fin.ext
    rfl
  rw [hmid, hmid]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  exact reservoirClassLocalMatching_coordinate (fieldsLen (selectiveLen p X)) H hfit p.wc hw k mate hinv _

end
end IntegerMultBounds.MathlibTM2.Routing
