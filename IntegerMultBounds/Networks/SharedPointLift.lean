import IntegerMultBounds.Networks.SharedPointKey
import IntegerMultBounds.Networks.MaskSignature
import IntegerMultBounds.Networks.PairMask

/-! Lift certified local pair supports through the actual omitted-point
coordinate map. Exact core and union formulas transport the small checked
signatures into the global equal-support sharing criterion. -/

namespace IntegerMultBounds.Networks.SharedPointLift

open NeighborCounts SharedPointMap

variable {width n : ℕ}

/-- Insert the common point after embedding the two local endpoints. -/
def source (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (i : Fin width) : Triple (n+1) :=
  insertTriple c ⟨(payload i).image c.succAbove,
    by rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective, hpair],
    by simp⟩

@[simp] theorem source_val (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (i : Fin width) :
    (source payload hpair c i).val = insert c ((payload i).image c.succAbove) := rfl

/-- The support is the image of the original source IDs, with no multiplicity loss. -/
def lift (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (support : Finset (Fin width)) : Finset (Triple (n+1)) :=
  support.image (source payload hpair c)

theorem source_injective (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (hinj : Function.Injective payload) (c : Fin (n+1)) : Function.Injective (source payload hpair c) := by
  intro i j he
  have hp := insertTriple_injective c he
  have hp' := congrArg Subtype.val hp
  exact hinj ((Finset.image_injective Fin.succAbove_right_injective) hp')

theorem lift_injective (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (hinj : Function.Injective payload) (c : Fin (n+1)) : Function.Injective (lift payload hpair c) :=
  Finset.image_injective (source_injective payload hpair hinj c)

theorem lift_card (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (hinj : Function.Injective payload) (c : Fin (n+1)) (support : Finset (Fin width)) :
    (lift payload hpair c support).card = support.card :=
  Finset.card_image_of_injective _ (source_injective payload hpair hinj c)

theorem common_mem (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (support : Finset (Fin width)) (T : Triple (n+1))
    (hT : T ∈ lift payload hpair c support) : c ∈ T.val := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
  simp

/-- Common-point insertion commutes with the complete core intersection,
including the empty-support case. -/
theorem core_lift (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (support : Finset (Fin width)) :
    SharedPointKey.core (lift payload hpair c support) =
      insert c ((MaskSignature.core payload support).image c.succAbove) := by
  ext v
  by_cases hv : v = c
  · subst v
    simp only [SharedPointKey.mem_core, Finset.mem_insert_self, iff_true]
    exact common_mem payload hpair c support
  · obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq hv
    simp only [SharedPointKey.mem_core, lift, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, source_val, Finset.mem_insert, Fin.succAbove_ne, false_or,
      Fin.succAbove_right_inj, exists_eq_right, MaskSignature.core,
      Finset.mem_filter, Finset.mem_univ, true_and]

/-- The common point occurs in the vertex union exactly when a source exists. -/
theorem vertices_lift (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c : Fin (n+1)) (support : Finset (Fin width)) (hne : support.Nonempty) :
    SharedPointKey.vertices (lift payload hpair c support) =
      insert c ((MaskSignature.union payload support).image c.succAbove) := by
  ext v
  simp only [SharedPointKey.mem_vertices, lift, Finset.mem_image, exists_exists_and_eq_and,
    source_val, Finset.mem_insert, MaskSignature.union, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hv | ⟨u, hu, he⟩⟩
    · exact Or.inl hv
    · exact Or.inr ⟨u, ⟨i, hi, hu⟩, he⟩
  · rintro (rfl | ⟨u, ⟨i, hi, hu⟩, he⟩)
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr ⟨u, hu, he⟩⟩

/-- Exact checked small signatures determine equal global support keys. -/
theorem equal_of_signatures (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c d : Fin (n+1)) (s t : Finset (Fin width)) (hs : s.Nonempty) (ht : t.Nonempty)
    (cs us ct ut : Finset (Fin n))
    (hcs : MaskSignature.core payload s = cs) (hus : MaskSignature.union payload s = us)
    (hct : MaskSignature.core payload t = ct) (hut : MaskSignature.union payload t = ut)
    (hc : insert c (cs.image c.succAbove) = insert d (ct.image d.succAbove))
    (hu : insert c (us.image c.succAbove) = insert d (ut.image d.succAbove))
    (hsize : 2 ≤ (insert c (cs.image c.succAbove)).card) :
    lift payload hpair c s = lift payload hpair d t := by
  apply SharedPointKey.key_injective
  · simpa only [core_lift, hcs] using hsize
  · apply Prod.ext
    · simpa only [SharedPointKey.key, core_lift, hcs, hct] using hc
    · simpa only [SharedPointKey.key, vertices_lift payload hpair c s hs,
        vertices_lift payload hpair d t ht, hus, hut] using hu


/-- A nonempty local core gives the two common vertices needed for key sharing. -/
theorem lifted_core_card (c : Fin (n+1)) (core : Finset (Fin n)) (hc : core.Nonempty) :
    2 ≤ (insert c (core.image c.succAbove)).card := by
  have hnot : c ∉ core.image c.succAbove := by simp
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  have hh := Finset.card_pos.mpr hc
  omega

/-- Direct interface for two rows carrying checked local vertex signatures. -/
theorem equal_of_correct (payload : Fin width → Finset (Fin n)) (hpair : ∀ i, (payload i).card = 2)
    (c d : Fin (n+1)) (left right : MaskDAG.Entry width)
    (ls rs : MaskSignature.Signature n)
    (hl : MaskSignature.Correct payload left ls) (hr : MaskSignature.Correct payload right rs)
    (hneL : (MaskDAG.decode left.mask).Nonempty) (hneR : (MaskDAG.decode right.mask).Nonempty)
    (hcore : (MaskDAG.decode ls.core).Nonempty)
    (hc : insert c ((MaskDAG.decode ls.core).image c.succAbove) =
      insert d ((MaskDAG.decode rs.core).image d.succAbove))
    (hu : insert c ((MaskDAG.decode ls.union).image c.succAbove) =
      insert d ((MaskDAG.decode rs.union).image d.succAbove)) :
    lift payload hpair c (MaskDAG.decode left.mask) = lift payload hpair d (MaskDAG.decode right.mask) :=
  equal_of_signatures payload hpair c d _ _ hneL hneR _ _ _ _
    hl.1.symm hl.2.symm hr.1.symm hr.2.symm hc hu (lifted_core_card c _ hcore)

/-- Bounds and canonical orientation of the source pair at a bit position. -/
theorem pairAt_bounds (n : ℕ) (i : Fin (n.choose 2)) :
    (PairMask.pairAt n i).1 < n ∧ (PairMask.pairAt n i).2 < n ∧
      (PairMask.pairAt n i).1 < (PairMask.pairAt n i).2 := by
  have hh := (PairedCoarseSupport.mem_pairs_sorted _ List.pairwise_lt_range _ _).mp
    (PairMask.pairAt_mem n i)
  simpa only [List.mem_range, PairMask.pairAt, List.get_eq_getElem] using hh

def pairLeft (n : ℕ) (i : Fin (n.choose 2)) : Fin n := ⟨(PairMask.pairAt n i).1, (pairAt_bounds n i).1⟩
def pairRight (n : ℕ) (i : Fin (n.choose 2)) : Fin n := ⟨(PairMask.pairAt n i).2, (pairAt_bounds n i).2.1⟩

/-- The exact local two-vertex payload in canonical source-bit order. -/
def pairPayload (n : ℕ) (i : Fin (n.choose 2)) : Finset (Fin n) := {pairLeft n i, pairRight n i}

theorem pairPayload_card (n : ℕ) (i : Fin (n.choose 2)) : (pairPayload n i).card = 2 := by
  have hne : pairLeft n i ≠ pairRight n i := by
    intro he
    have hh := congrArg Fin.val he
    have hl := (pairAt_bounds n i).2.2
    simp only [pairLeft, pairRight] at hh
    omega
  simp [pairPayload, hne]

/-- Compatibility with the source payload used by the small-signature checker. -/
theorem pairPayload_eq_filter (n : ℕ) (i : Fin (n.choose 2)) :
    pairPayload n i = Finset.univ.filter (fun v : Fin n =>
      v.val = (PairMask.pairAt n i).1 ∨ v.val = (PairMask.pairAt n i).2) := by
  ext v
  simp [pairPayload, pairLeft, pairRight, Fin.ext_iff]

theorem pairPayload_injective (n : ℕ) : Function.Injective (pairPayload n) := by
  intro i j he
  have hi := (pairAt_bounds n i).2.2
  have hj := (pairAt_bounds n j).2.2
  have hleft : pairLeft n i = pairLeft n j ∨ pairLeft n i = pairRight n j := by
    have hh : pairLeft n i ∈ pairPayload n j := by rw [← he]; simp [pairPayload]
    simpa [pairPayload] using hh
  have hright : pairRight n i = pairLeft n j ∨ pairRight n i = pairRight n j := by
    have hh : pairRight n i ∈ pairPayload n j := by rw [← he]; simp [pairPayload]
    simpa [pairPayload] using hh
  apply PairMask.pairAt_injective n
  rcases hleft with hl | hl <;> rcases hright with hr | hr
  all_goals
    have hl' := congrArg Fin.val hl
    have hr' := congrArg Fin.val hr
    simp only [pairLeft, pairRight] at hl' hr'
    apply Prod.ext <;> omega

/-- Concrete local support lifting from49 vertices to50 uses the same succAbove
order as deleting one element of range50 in the upstream shared circuit. -/
abbrev lift49 (c : Fin 50) (support : Finset (Fin 1176)) : Finset (Triple 50) :=
  lift (pairPayload 49) (pairPayload_card 49) c support

theorem lift49_injective (c : Fin 50) : Function.Injective (lift49 c) :=
  lift_injective _ _ (pairPayload_injective 49) c

theorem lift49_card (c : Fin 50) (support : Finset (Fin 1176)) : (lift49 c support).card = support.card :=
  lift_card _ _ (pairPayload_injective 49) c support

end IntegerMultBounds.Networks.SharedPointLift
