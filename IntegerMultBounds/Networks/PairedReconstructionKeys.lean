import IntegerMultBounds.Networks.PairedCircuitCorrect

/-! Exact key coverage of the concrete paired reconstruction loops. -/

namespace IntegerMultBounds.Networks.PairedReconstructionKeys

open PairedCircuit PairedCircuitCorrect

@[simp] theorem groupAt_zero (g : List ℕ) (gs : List (List ℕ)) : groupAt (g :: gs) 0 = g := rfl
@[simp] theorem groupAt_succ (g : List ℕ) (gs : List (List ℕ)) (i : ℕ) :
    groupAt (g :: gs) (i + 1) = groupAt gs i := rfl

theorem range_groupAt (gs : List (List ℕ)) :
    (List.range gs.length).map (groupAt gs) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, groupAt_zero, groupAt_succ, ih]

@[simp] theorem members_snd (gs : List (List ℕ)) : (members gs).map Prod.snd = gs.flatten := by
  simp only [members, List.map_flatMap, List.map_map, Function.comp_def, List.map_id']
  rw [List.flatMap_def, range_groupAt]

@[simp] theorem members_groups (points : List ℕ) :
    (members (PairGrouping.groups points)).map Prod.snd = points := by
  rw [members_snd, PairGrouping.flatten_groups]

theorem pairs_map (f : ℕ → ℕ) (xs : List ℕ) :
    pairs (xs.map f) = (pairs xs).map (fun p => (f p.1, f p.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih, List.map_map, Function.comp_def]

/-- Crossing keys in the same group-pair order as the implementation. -/
def crossLists : List (List ℕ) → List (ℕ × ℕ)
  | [] => []
  | g :: gs => gs.flatMap (fun h => g.flatMap (fun a => h.map (a, ·))) ++ crossLists gs

theorem crossKeys_eq (gs : List (List ℕ)) :
    (pairs (List.range gs.length)).flatMap (crossGroupKeys gs) = crossLists gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, pairs, pairs_map,
      List.flatMap_append, List.flatMap_map, crossGroupKeys,
      groupAt_zero, groupAt_succ, crossLists]
    change (List.range gs.length).flatMap (fun i => g.flatMap (fun a => (groupAt gs i).map (a, ·))) ++
      (pairs (List.range gs.length)).flatMap (crossGroupKeys gs) = _
    rw [ih]
    congr 1
    simpa only [List.flatMap_map] using
      congrArg (fun hs : List (List ℕ) => hs.flatMap (fun h => g.flatMap (fun a => h.map (a, ·))))
        (range_groupAt gs)

theorem internalKeys_eq (gs : List (List ℕ)) (outside : WeightTable) :
    (internalPairs gs outside).map Prod.fst = gs.flatMap pairs := by
  simp only [internalPairs, List.map_flatMap, List.map_map, Function.comp_def, List.map_id']
  simpa only [List.flatMap_map] using congrArg (List.flatMap pairs) (range_groupAt gs)


private theorem crossHead_perm (g : List ℕ) (gs : List (List ℕ)) :
    (gs.flatMap (fun h => g.flatMap (fun a => h.map (a, ·)))).Perm
      (g.flatMap (fun a => gs.flatten.map (a, ·))) := by
  induction gs with
  | nil => simp
  | cons h gs ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.map_append]
    exact (ih.append_left _).trans (List.flatMap_append_perm g _ _)

private theorem pairs_append_perm (xs ys : List ℕ) :
    (pairs xs ++ xs.flatMap (fun a => ys.map (a, ·)) ++ pairs ys).Perm (pairs (xs ++ ys)) := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    simp only [pairs, List.flatMap_cons, List.cons_append, List.map_append, List.append_assoc]
    apply List.Perm.append_left
    refine (List.perm_append_comm_assoc _ _ _).trans ?_
    simpa only [List.append_assoc] using ih.append_left (ys.map (x, ·))

/-- Internal and crossing loops enumerate every ordered input pair exactly
once, although their evaluation order differs from the canonical pair list. -/
theorem allKeys_perm (gs : List (List ℕ)) :
    (gs.flatMap pairs ++ crossLists gs).Perm (pairs gs.flatten) := by
  induction gs with
  | nil => simp [crossLists, pairs]
  | cons g gs ih =>
    simp only [List.flatMap_cons, crossLists, List.flatten_cons, List.append_assoc]
    have hm := (List.perm_append_comm_assoc (gs.flatMap pairs)
      (gs.flatMap (fun h => g.flatMap (fun a => h.map (a, ·)))) (crossLists gs)).append_left (pairs g)
    refine hm.trans ?_
    have hr := (crossHead_perm g gs).append ih
    have hp := hr.append_left (pairs g)
    exact hp.trans (by simpa only [List.append_assoc] using pairs_append_perm g gs.flatten)

/-- The actual reconstruction tables cover the canonical fine pair keys. -/
theorem reconstructionKeys_perm (points : List ℕ) (outside : WeightTable) :
    ((internalPairs (PairGrouping.groups points) outside).map Prod.fst ++
      (pairs (List.range (PairGrouping.groups points).length)).flatMap
        (crossGroupKeys (PairGrouping.groups points))).Perm (pairs points) := by
  rw [internalKeys_eq, crossKeys_eq]
  simpa only [PairGrouping.flatten_groups] using allKeys_perm (PairGrouping.groups points)

end IntegerMultBounds.Networks.PairedReconstructionKeys
