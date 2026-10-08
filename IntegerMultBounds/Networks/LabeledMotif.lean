import IntegerMultBounds.Networks.GroupedFrames
import IntegerMultBounds.Networks.MotifSupport
import IntegerMultBounds.Networks.MotifLabels

/-! Actual motif groups equipped with their common tensor-subspace labels.
Forward and opposite-inverse schedules retain all scalar boundaries. Their
actual RankTrace histories are comparable, including explicit output edges.
The exact loss comes only from covered central columns and is at most the
number of central registers times the current-factor dimension. -/

namespace IntegerMultBounds.Networks.LabeledMotif

open GroupedCircuit GroupedFrames Circuit MotifLabels
open Module

section Histories
variable {ι L R : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]

/-- One label per actual incident group. Repeated scalar incidences in the
same group are represented once; they all use this same label. -/
def history (vs : List (Vertex ι L R)) (i : ι) : List L :=
  vs.filterMap fun v => if i ∈ touched v.group then some v.label else none

@[simp] theorem history_append (vs ws : List (Vertex ι L R)) (i : ι) :
    history (vs ++ ws) i = history vs i ++ history ws i := List.filterMap_append

@[simp] theorem history_nil (i : ι) : history ([] : List (Vertex ι L R)) i = [] := rfl

@[simp] theorem history_cons (v : Vertex ι L R) (vs : List (Vertex ι L R)) (i : ι) :
    history (v :: vs) i =
      (if i ∈ touched v.group then [v.label] else []) ++ history vs i := by
  simp only [history, List.filterMap_cons]
  split_ifs <;> rfl

theorem history_ofFn_absent {n : ℕ} (vs : Fin n → Vertex ι L R) (i : ι)
    (h : ∀ j, i ∉ touched (vs j).group) : history (List.ofFn vs) i = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro v hv
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
  simp [h j]

private theorem select_one {I : Type*} [DecidableEq I] (xs : List I) (hn : xs.Nodup)
    (k : I) (f : I → L) :
    (xs.filterMap fun j => if j = k then some (f j) else none) =
      if k ∈ xs then [f k] else [] := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    have hn' := List.nodup_cons.mp hn
    rw [List.filterMap_cons]
    by_cases hj : j = k
    · subst j
      simp [ih hn'.2, hn'.1]
    · simp [hj, ih hn'.2, Ne.symm hj]

theorem history_ofFn_unique {n : ℕ} (vs : Fin n → Vertex ι L R) (i : ι) (k : Fin n)
    (h : ∀ j, i ∈ touched (vs j).group ↔ j = k) :
    history (List.ofFn vs) i = [(vs k).label] := by
  have he : List.ofFn vs = (List.ofFn fun j : Fin n => j).map vs := by simp only [List.map_ofFn]; rfl
  rw [history, he, List.filterMap_map]
  simp only [Function.comp_def, h]
  simpa using select_one (List.ofFn fun j : Fin n => j)
    (List.nodup_ofFn.mpr (fun _ _ h => h)) k (fun j => (vs j).label)

theorem history_ofFn_optional {n : ℕ} (vs : Fin n → Vertex ι L R) (i : ι) (k : Fin n)
    (P : Prop) [Decidable P] (h : ∀ j, i ∈ touched (vs j).group ↔ j = k ∧ P) :
    history (List.ofFn vs) i = if P then [(vs k).label] else [] := by
  by_cases hp : P
  · rw [ite_eq_left hp]
    exact history_ofFn_unique vs i k (by intro j; simpa [hp] using h j)
  · rw [ite_eq_right hp]
    exact history_ofFn_absent vs i (by intro j; simp [h j, hp])

/-- Last physical label after all actual groups agrees with the extracted
incident-group history, despite duplicate incidences in a group. -/
theorem finalLabels_history (current : ι → L) (vs : List (Vertex ι L R)) (i : ι) :
    finalLabels current vs i = (history vs i).getLast?.getD (current i) := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih =>
    rw [finalLabels, ih, history_cons]
    have ha : after current v i = if i ∈ touched v.group then v.label else current i :=
      RankTrace.finish_align current (fun _ => v.label) (touched v.group) i
    rw [ha]
    by_cases hi : i ∈ touched v.group
    · simp only [hi, ↓reduceIte, List.singleton_append]
      cases hh : history vs i with
      | nil => rfl
      | cons l ls => simp [List.getLast?_eq_some_getLast (List.cons_ne_nil l ls)]
    · simp [hi]

/-- Sum of the actual downward dimension changes along a single wire. -/
def pathLoss (d : L → ℕ) : L → List L → ℕ
  | _, [] => 0
  | current, next :: rest => d current - d next + pathLoss d next rest

theorem loss_append (d : L → ℕ) (current : ι → L) (xs ys : List (ι × L)) :
    RankTrace.loss d current (xs ++ ys) = RankTrace.loss d current xs +
      RankTrace.loss d (RankTrace.finish current xs) ys := by
  simp [RankTrace.loss, RankTrace.edges_append]

/-- Repeated incidences on a wire in one alignment contribute zero after its
first occurrence, so the exact loss sums once over its physical support. -/
theorem loss_align [Fintype ι] (d : L → ℕ) (current desired : ι → L) (wires : List ι) :
    RankTrace.loss d current (wires.map fun i => (i, desired i)) =
      ∑ i, if i ∈ wires then d (current i) - d (desired i) else 0 := by
  induction wires generalizing current with
  | nil => simp [RankTrace.loss, RankTrace.edges]
  | cons j wires ih =>
    change d (current j) - d (desired j) +
      RankTrace.loss d (Function.update current j (desired j))
        (wires.map fun i => (i, desired i)) = _
    rw [ih]
    have hp (i : ι) :
        (if i ∈ j :: wires then d (current i) - d (desired i) else 0) =
        (if i = j then d (current j) - d (desired j) else 0) +
        (if i ∈ wires then d (Function.update current j (desired j) i) - d (desired i) else 0) := by
      by_cases hij : i = j
      · subst i; simp
      · simp [hij]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    simp

/-- Exact decomposition of the compiler's RankTrace loss into the actual
incident-group histories. No inferred or assumed history appears here. -/
theorem loss_history [Fintype ι] (d : L → ℕ) (current : ι → L)
    (vs : List (Vertex ι L R)) :
    RankTrace.loss d current (updates vs) = ∑ i, pathLoss d (current i) (history vs i) := by
  induction vs generalizing current with
  | nil => simp [updates, RankTrace.loss, RankTrace.edges, pathLoss]
  | cons v vs ih =>
    change RankTrace.loss d current (touches v ++ updates vs) = _
    rw [loss_append, ih]
    change RankTrace.loss d current ((touched v.group).map fun i => (i, v.label)) + _ = _
    rw [loss_align, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if i ∈ touched v.group then d (current i) - d v.label else 0) +
      pathLoss d (after current v i) (history vs i) = _
    have ha : after current v i = if i ∈ touched v.group then v.label else current i :=
      RankTrace.finish_align current (fun _ => v.label) (touched v.group) i
    rw [ha, history_cons]
    by_cases hi : i ∈ touched v.group <;> simp [hi, pathLoss]

/-- A consecutive-pair relation on a wire's actual incident groups. -/
def pathRel (rel : L → L → Prop) : L → List L → Prop
  | _, [] => True
  | current, next :: rest => rel current next ∧ pathRel rel next rest

theorem edges_align_rel (rel : L → L → Prop) (hrefl : ∀ l, rel l l)
    (current : ι → L) (next : L) (wires : List ι)
    (h : ∀ i ∈ wires, rel (current i) next) :
    ∀ p ∈ RankTrace.edges current (wires.map fun i => (i, next)), rel p.1 p.2 := by
  induction wires generalizing current with
  | nil => simp [RankTrace.edges]
  | cons i wires ih =>
    intro p hp
    simp only [List.map_cons, RankTrace.edges, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h i (by simp)
    · apply ih (Function.update current i next) _ p hp
      intro j hj
      by_cases he : j = i
      · subst j; simpa using hrefl next
      · simpa [he] using h j (by simp [hj])

/-- A relation proved from actual group incidences holds on every actual
RankTrace edge, including repeated incidences within individual groups. -/
theorem edges_history_rel (rel : L → L → Prop) (hrefl : ∀ l, rel l l)
    (current : ι → L) (vs : List (Vertex ι L R))
    (h : ∀ i, pathRel rel (current i) (history vs i)) :
    ∀ p ∈ RankTrace.edges current (updates vs), rel p.1 p.2 := by
  induction vs generalizing current with
  | nil => simp [updates, RankTrace.edges]
  | cons v vs ih =>
    have hfirst (i : ι) (hi : i ∈ touched v.group) : rel (current i) v.label := by
      have hh := h i
      simp only [history_cons, hi, ↓reduceIte, List.singleton_append, pathRel] at hh
      exact hh.1
    have hrest (i : ι) : pathRel rel (after current v i) (history vs i) := by
      have hh := h i
      have ha : after current v i = if i ∈ touched v.group then v.label else current i :=
        RankTrace.finish_align current (fun _ => v.label) (touched v.group) i
      rw [ha]
      by_cases hi : i ∈ touched v.group
      · simp only [hi, ↓reduceIte]
        have hh' : rel (current i) v.label ∧ pathRel rel v.label (history vs i) := by
          simpa only [history_cons, hi, ↓reduceIte, List.singleton_append, pathRel] using hh
        exact hh'.2
      · simpa only [history_cons, hi, ↓reduceIte, List.nil_append] using hh
    intro p hp
    change p ∈ RankTrace.edges current (touches v ++ updates vs) at hp
    rw [RankTrace.edges_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact edges_align_rel rel hrefl current v.label (touched v.group) hfirst p hp
    · exact ih (after current v) hrest p hp

/-- Aligning to per-wire endpoints preserves a reflexive relation whenever
its starting endpoint comparisons hold. -/
theorem edges_endpoints_rel (rel : L → L → Prop) (hrefl : ∀ l, rel l l)
    (current desired : ι → L) (wires : List ι)
    (h : ∀ i ∈ wires, rel (current i) (desired i)) :
    ∀ p ∈ RankTrace.edges current (wires.map fun i => (i, desired i)), rel p.1 p.2 := by
  induction wires generalizing current with
  | nil => simp [RankTrace.edges]
  | cons i wires ih =>
    intro p hp
    simp only [List.map_cons, RankTrace.edges, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h i (by simp)
    · apply ih (Function.update current i (desired i)) _ p hp
      intro j hj
      by_cases he : j = i
      · subst j; simpa using hrefl (desired i)
      · simpa [he] using h j (by simp [hj])

end Histories

section Schedules
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R]
  {n a c s : ℕ}

private theorem sx (i : Fin a) (j : Fin n) :
    (side i : Role n a c s) ≠ x j := by simp [side, x]
private theorem ys (i : Fin n) (j : Fin a) :
    (y i : Role n a c s) ≠ side j := by simp [y, side]
private theorem yc (i : Fin n) (j : Fin c) :
    (y i : Role n a c s) ≠ center j := by simp [y, center]
private theorem cx (i : Fin c) (j : Fin n) :
    (center i : Role n a c s) ≠ x j := by simp [center, x]

variable (g : Geometry K E F) (t : Fin n → F)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

open scoped TensorProduct

/-- The literal eight rows, each group carrying its manuscript subspace. -/
def forward : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (List.ofFn fun j : Fin n =>
    ⟨faninGroup (y j) side ((-J) j) (ys j), g.yIn (t j)⟩) ++
  [⟨matrixGroup y center (-H) yc, g.common⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨copyGroup side x owner 1 sx j, g.xMiddle (t j)⟩) ++
  [⟨matrixGroup center x G cx, g.full⟩] ++
  [⟨matrixGroup y center H yc, g.common⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨faninGroup (y j) side (J j) (ys j), g.yOut (t j)⟩) ++
  [⟨matrixGroup center x (-G) cx, g.full⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨copyGroup side x owner (-1) sx j, g.full⟩)

/-- Forgetting labels recovers exactly the proved scalar grouped schedule. -/
theorem forward_groups :
    (forward (s := s) g t owner G J H).map Vertex.group = dirtyGroups owner G J H := by
  simp only [forward, dirtyGroups, copyGroups, faninGroups, List.map_append,
    List.map_cons, List.map_nil, List.map_ofFn]
  rfl

/-- Middle inverse before exchanging names; labels already refer to physical
X/Y banks after the exchange. -/
def inverse : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (List.ofFn fun j : Fin n =>
    ⟨copyGroup side x owner 1 sx j, g.yIn (t j)⟩) ++
  [⟨matrixGroup center x G cx, g.common⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨faninGroup (y j) side ((-J) j) (ys j), g.xMiddle (t j)⟩) ++
  [⟨matrixGroup y center (-H) yc, g.full⟩] ++
  [⟨matrixGroup center x (-G) cx, g.common⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨copyGroup side x owner (-1) sx j, g.yOut (t j)⟩) ++
  [⟨matrixGroup y center H yc, g.full⟩] ++
  (List.ofFn fun j : Fin n =>
    ⟨faninGroup (y j) side (J j) (ys j), g.full⟩)

theorem inverse_groups :
    (inverse (s := s) g t owner G J H).map Vertex.group = dirtyInverseGroups owner G J H := by
  simp only [inverse, dirtyInverseGroups, copyGroups, faninGroups, List.map_append,
    List.map_cons, List.map_nil, List.map_ofFn]
  rfl

/-- The actual middle inverse, with physical data-bank names exchanged. -/
def opposite : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (inverse g t owner G J H).map fun v => ⟨v.group.rename (exchangeRoles n a c s), v.label⟩

theorem opposite_groups :
    (opposite (s := s) g t owner G J H).map Vertex.group = oppositeGroups owner G J H := by
  rw [opposite, List.map_map, oppositeGroups, renameGroups, ← inverse_groups g t owner G J H,
    List.map_map]
  rfl

private theorem fan_y (M : Fin n → Fin a → R)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (j : Fin n) :
    history (List.ofFn fun i : Fin n =>
      (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ : Vertex (Role n a c s) _ R)) (y j) =
      [labels j] := by
  apply history_ofFn_unique _ _ j
  intro i
  simp [faninGroup_touched, y, side, eq_comm]

private theorem fan_x (M : Fin n → Fin a → R)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (j : Fin n) :
    history (List.ofFn fun i : Fin n =>
      (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ : Vertex (Role n a c s) _ R)) (x j) =
      [] := by
  apply history_ofFn_absent
  intro i
  simp [faninGroup_touched, x, y, side]

private theorem copy_x (r : R) (hr : r ≠ 0)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (j : Fin n) :
    history (List.ofFn fun i : Fin n =>
      (⟨copyGroup side x owner r sx i, labels i⟩ : Vertex (Role n a c s) _ R)) (x j) =
      if ∃ p, owner p = j then [labels j] else [] := by
  apply history_ofFn_optional _ _ j
  intro i
  rw [copyGroup_touched _ _ _ _ hr]
  simp only [x, side, Sum.inl.injEq, reduceCtorEq]
  aesop

private theorem copy_y (r : R)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (j : Fin n) :
    history (List.ofFn fun i : Fin n =>
      (⟨copyGroup side x owner r sx i, labels i⟩ : Vertex (Role n a c s) _ R)) (y j) =
      [] := by
  apply history_ofFn_absent
  intro i
  simp [copyGroup, fanoutGroup_touched, x, y, side]

private theorem fan_side (M : Fin n → Fin a → R)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (p : Fin a) (target : Fin a → Fin n)
    (hM : ∀ i p, M i p ≠ 0 ↔ target p = i) :
    history (List.ofFn fun i : Fin n =>
      (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ : Vertex (Role n a c s) _ R)) (side p) =
      [labels (target p)] := by
  apply history_ofFn_unique _ _ (target p)
  intro i
  simp [faninGroup_touched, y, side, hM, eq_comm]

private theorem copy_side (r : R) (hr : r ≠ 0)
    (labels : Fin n → Submodule K (E ⊗[K] F)) (p : Fin a) :
    history (List.ofFn fun i : Fin n =>
      (⟨copyGroup side x owner r sx i, labels i⟩ : Vertex (Role n a c s) _ R)) (side p) =
      [labels (owner p)] := by
  apply history_ofFn_unique _ _ (owner p)
  intro i
  rw [copyGroup_touched _ _ _ _ hr]
  simp [side, x, eq_comm]

/-- Forward data X sees only its optional copy and gather incidences. -/
theorem forward_x_history [Nontrivial R] (j : Fin n) :
    history (forward (s := s) g t owner G J H) (x j) =
      (if ∃ p, owner p = j then [g.xMiddle (t j)] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.full] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.full] else []) ++
      (if ∃ p, owner p = j then [g.full] else []) := by
  simp only [forward, history_append, fan_x, copy_x owner (1 : R) one_ne_zero,
    copy_x owner (-1 : R) (neg_ne_zero.mpr one_ne_zero), history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, x, y, center, List.append_assoc]

/-- Forward data Y sees all four of its target-owned incidences. -/
theorem forward_y_history (j : Fin n) :
    history (forward (s := s) g t owner G J H) (y j) =
      [g.yIn (t j), g.common, g.common, g.yOut (t j)] := by
  simp only [forward, history_append, fan_y, copy_y, history_cons, history_nil,
    List.append_nil]
  simp [matrixGroup_touched, x, y, center]

/-- Every forward side wire has its exact owner-dependent four-row history. -/
theorem forward_side_history [Nontrivial R] (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i) (p : Fin a) :
    history (forward (s := s) g t owner G J H) (side p) =
      [g.yIn (t (target p)), g.xMiddle (t (owner p)), g.yOut (t (target p)), g.full] := by
  have hn : ∀ i p, (-J) i p ≠ 0 ↔ target p = i := by simpa using hJ
  simp only [forward, history_append, fan_side _ _ p target hn,
    fan_side _ _ p target hJ, copy_side owner (1 : R) one_ne_zero,
    copy_side owner (-1 : R) (neg_ne_zero.mpr one_ne_zero), history_cons, history_nil,
    List.append_nil]
  simp [matrixGroup_touched, x, y, center, side]

/-- Inverse logical X is physical Y and can skip absent owner incidences. -/
theorem inverse_x_history [Nontrivial R] (j : Fin n) :
    history (inverse (s := s) g t owner G J H) (x j) =
      (if ∃ p, owner p = j then [g.yIn (t j)] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.common] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.common] else []) ++
      (if ∃ p, owner p = j then [g.yOut (t j)] else []) := by
  simp only [inverse, history_append, fan_x, copy_x owner (1 : R) one_ne_zero,
    copy_x owner (-1 : R) (neg_ne_zero.mpr one_ne_zero), history_cons, history_nil,
    List.append_nil]
  simp [matrixGroup_touched, x, y, center, List.append_assoc]

/-- Inverse logical Y is physical X and has all four target incidences. -/
theorem inverse_y_history (j : Fin n) :
    history (inverse (s := s) g t owner G J H) (y j) =
      [g.xMiddle (t j), g.full, g.full, g.full] := by
  simp only [inverse, history_append, fan_y, copy_y, history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, x, y, center]

/-- The middle inverse reverses the side wire's physical X/Y owners. -/
theorem inverse_side_history [Nontrivial R] (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i) (p : Fin a) :
    history (inverse (s := s) g t owner G J H) (side p) =
      [g.yIn (t (owner p)), g.xMiddle (t (target p)), g.yOut (t (owner p)), g.full] := by
  have hn : ∀ i p, (-J) i p ≠ 0 ↔ target p = i := by simpa using hJ
  simp only [inverse, history_append, fan_side _ _ p target hn,
    fan_side _ _ p target hJ, copy_side owner (1 : R) one_ne_zero,
    copy_side owner (-1 : R) (neg_ne_zero.mpr one_ne_zero), history_cons, history_nil,
    List.append_nil]
  simp [matrixGroup_touched, x, y, center, side]

/-- A central wire is incident precisely at the four central rows; empty
scatter columns remove both of their incidences. -/
theorem forward_center_history (j : Fin c) :
    history (forward (s := s) g t owner G J H) (center j) =
      (if ∃ i, H i j ≠ 0 then [g.common] else []) ++ [g.full] ++
      (if ∃ i, H i j ≠ 0 then [g.common] else []) ++ [g.full] := by
  have hfan (M : Fin n → Fin a → R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ :
          Vertex (Role n a c s) _ R)) (center j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [faninGroup_touched, center, y, side]
  have hcopy (r : R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨copyGroup side x owner r sx i, labels i⟩ :
          Vertex (Role n a c s) _ R)) (center j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [copyGroup, fanoutGroup_touched, center, side, x]
  simp only [forward, history_append, hfan, hcopy, history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, center, x, y, Pi.neg_apply, List.append_assoc]

/-- The inverse's central history uses the same common/full labels in the
same order; its empty scatter columns remove the full-label incidences. -/
theorem inverse_center_history (j : Fin c) :
    history (inverse (s := s) g t owner G J H) (center j) =
      [g.common] ++ (if ∃ i, H i j ≠ 0 then [g.full] else []) ++
      [g.common] ++ (if ∃ i, H i j ≠ 0 then [g.full] else []) := by
  have hfan (M : Fin n → Fin a → R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ :
          Vertex (Role n a c s) _ R)) (center j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [faninGroup_touched, center, y, side]
  have hcopy (r : R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨copyGroup side x owner r sx i, labels i⟩ :
          Vertex (Role n a c s) _ R)) (center j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [copyGroup, fanoutGroup_touched, center, side, x]
  simp only [inverse, history_append, hfan, hcopy, history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, center, x, y, Pi.neg_apply, List.append_assoc]

/-- Unused physical spectator registers acquire no motif labels. -/
theorem forward_spectator_history (j : Fin s) :
    history (forward g t owner G J H) (spectator j) = [] := by
  have hfan (M : Fin n → Fin a → R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ :
          Vertex (Role n a c s) _ R)) (spectator j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [faninGroup_touched, spectator, y, side]
  have hcopy (r : R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨copyGroup side x owner r sx i, labels i⟩ :
          Vertex (Role n a c s) _ R)) (spectator j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [copyGroup, fanoutGroup_touched, spectator, side, x]
  simp only [forward, history_append, hfan, hcopy, history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, spectator, x, y, center]

theorem inverse_spectator_history (j : Fin s) :
    history (inverse g t owner G J H) (spectator j) = [] := by
  have hfan (M : Fin n → Fin a → R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨faninGroup (y i) side (M i) (ys i), labels i⟩ :
          Vertex (Role n a c s) _ R)) (spectator j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [faninGroup_touched, spectator, y, side]
  have hcopy (r : R) (labels : Fin n → Submodule K (E ⊗[K] F)) :
      history (List.ofFn fun i : Fin n =>
        (⟨copyGroup side x owner r sx i, labels i⟩ :
          Vertex (Role n a c s) _ R)) (spectator j) = [] := by
    apply history_ofFn_absent
    intro i
    simp [copyGroup, fanoutGroup_touched, spectator, side, x]
  simp only [inverse, history_append, hfan, hcopy, history_cons, history_nil,
    List.append_nil, List.nil_append]
  simp [matrixGroup_touched, spectator, x, y, center]

/-- Role exchange preserves the full physical incidence history. -/
theorem opposite_history (i : Role n a c s) :
    history (opposite g t owner G J H) (exchangeRoles n a c s i) =
      history (inverse g t owner G J H) i := by
  unfold opposite
  generalize inverse (s := s) g t owner G J H = vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, history_cons]
    have hh := GroupedCircuit.touched_rename (exchangeRoles n a c s) v.group i
    simp only [ih]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (hh.mp h₁))
    · exact False.elim (h₁ (hh.mpr h₂))
    · rfl

/-- Physical source labels for one invocation; scratch and spectator labels
start at zero. The future tensor lift and stage isometry are separate. -/
def input : Role n a c s → Submodule K (E ⊗[K] F)
  | .inl j => g.xIn (t j)
  | .inr (.inl j) => g.yIn (t j)
  | .inr (.inr _) => ⊥

/-- Source labels in the logical inverse names, before physical bank exchange. -/
def inverseInput : Role n a c s → Submodule K (E ⊗[K] F)
  | .inl j => g.yIn (t j)
  | .inr (.inl j) => g.xIn (t j)
  | .inr (.inr _) => ⊥

/-- Data outputs and scratch endpoints; scratch is completed to the ambient
space after its last physical incidence. -/
def output : Role n a c s → Submodule K (E ⊗[K] F)
  | .inr (.inl j) => g.yOut (t j)
  | _ => ⊤

/-- Sparse omitted incidences only leave a smaller final subspace, so explicit
output alignment adds no decreasing transition. -/
theorem forward_final_le_output (i : Role n a c s) :
    finalLabels (input g t) (forward g t owner G J H) i ≤ output g t i := by
  rcases i with j | j | j
  · exact le_top
  · change finalLabels (input g t) (forward g t owner G J H) (y j) ≤ g.yOut (t j)
    rw [finalLabels_history, forward_y_history]
    simp
  · exact le_top

theorem opposite_final_le_output [Nontrivial R] (i : Role n a c s) :
    finalLabels (input g t) (opposite g t owner G J H) i ≤ output g t i := by
  rcases i with j | j | j
  · exact le_top
  · change finalLabels (input g t) (opposite g t owner G J H) (y j) ≤ g.yOut (t j)
    rw [finalLabels_history]
    change (history (opposite g t owner G J H) (exchangeRoles n a c s (x j))).getLast?.getD
      (g.yIn (t j)) ≤ g.yOut (t j)
    rw [opposite_history, inverse_x_history]
    have h₁ := g.common_le_yOut (t j)
    have h₂ := (g.yIn_le_common (t j)).trans h₁
    split_ifs <;> simp [h₁, h₂]
  · exact le_top

/-- Comparability means actual inclusion in one of the two directions. -/
def Comparable (U V : Submodule K (E ⊗[K] F)) : Prop := U ≤ V ∨ V ≤ U

section Comparability
variable [Nontrivial R]

theorem forward_histories_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0)
    (i : Role n a c s) :
    pathRel Comparable (input g t i) (history (forward g t owner G J H) i) := by
  rcases i with j | j | p | j | j
  · change pathRel Comparable (g.xIn (t j)) (history _ (x j))
    rw [forward_x_history]
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := g.middle_le_full (t j)
    have h₃ := h₁.trans h₂
    split_ifs <;> simp [pathRel, Comparable, h₁, h₂, h₃]
  · change pathRel Comparable (g.yIn (t j)) (history _ (y j))
    rw [forward_y_history]
    simp [pathRel, Comparable, g.yIn_le_common, g.common_le_yOut]
  · change pathRel Comparable ⊥ (history _ (side p))
    rw [forward_side_history g t owner G J H target hJ]
    have h₁ := (g.yIn_le_common (t (target p))).trans
      (show g.common ≤ g.xMiddle (t (owner p)) from le_sup_left)
    have h₂ := g.side_middle_le_out _ _ (hneigh p)
    simp [pathRel, Comparable, h₁, h₂, g.yOut_le_full]
  · change pathRel Comparable ⊥ (history _ (center j))
    rw [forward_center_history]
    split_ifs <;> simp [pathRel, Comparable, g.common_le_full]
  · change pathRel Comparable ⊥ (history _ (spectator j))
    rw [forward_spectator_history]
    trivial

theorem inverse_histories_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0)
    (i : Role n a c s) :
    pathRel Comparable (inverseInput g t i) (history (inverse g t owner G J H) i) := by
  rcases i with j | j | p | j | j
  · change pathRel Comparable (g.yIn (t j)) (history _ (x j))
    rw [inverse_x_history]
    have h₁ := g.yIn_le_common (t j)
    have h₂ := g.common_le_yOut (t j)
    have h₃ := h₁.trans h₂
    split_ifs <;> simp [pathRel, Comparable, h₁, h₂, h₃]
  · change pathRel Comparable (g.xIn (t j)) (history _ (y j))
    rw [inverse_y_history]
    simp [pathRel, Comparable, g.xIn_le_middle, g.middle_le_full]
  · change pathRel Comparable ⊥ (history _ (side p))
    rw [inverse_side_history g t owner G J H target hJ]
    have h₁ := (g.yIn_le_common (t (owner p))).trans
      (show g.common ≤ g.xMiddle (t (target p)) from le_sup_left)
    have h₂ := g.side_middle_le_out _ _ (hneigh p)
    simp [pathRel, Comparable, h₁, h₂, g.yOut_le_full]
  · change pathRel Comparable ⊥ (history _ (center j))
    rw [inverse_center_history]
    split_ifs <;> simp [pathRel, Comparable, g.common_le_full]
  · change pathRel Comparable ⊥ (history _ (spectator j))
    rw [inverse_spectator_history]
    trivial

theorem opposite_histories_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0)
    (i : Role n a c s) :
    pathRel Comparable (input g t i) (history (opposite g t owner G J H) i) := by
  obtain ⟨i, rfl⟩ := (exchangeRoles n a c s).surjective i
  rw [opposite_history]
  have hi : input g t (exchangeRoles n a c s i) = inverseInput g t i := by
    rcases i with j | j | j <;> rfl
  rw [hi]
  exact inverse_histories_comparable g t owner G J H target hJ hneigh i

/-- The actual forward RankTrace edges satisfy the projection-rank premise. -/
theorem forward_edges_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0) :
    ∀ p ∈ RankTrace.edges (input (s := s) g t) (updates (forward g t owner G J H)),
      Comparable p.1 p.2 :=
  edges_history_rel Comparable (fun _ => Or.inl le_rfl) _ _
    (forward_histories_comparable g t owner G J H target hJ hneigh)

/-- The middle opposite-inverse trace satisfies the same actual premise. -/
theorem opposite_edges_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0) :
    ∀ p ∈ RankTrace.edges (input (s := s) g t) (updates (opposite g t owner G J H)),
      Comparable p.1 p.2 :=
  edges_history_rel Comparable (fun _ => Or.inl le_rfl) _ _
    (opposite_histories_comparable g t owner G J H target hJ hneigh)

/-- Including explicit output edges, every forward projection difference has
comparable actual endpoint subspaces. -/
theorem forward_network_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0)
    (wires : List (Role n a c s)) :
    ∀ p ∈ RankTrace.edges (input g t)
      (networkUpdates wires (output g t) (forward g t owner G J H)), Comparable p.1 p.2 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact forward_edges_comparable g t owner G J H target hJ hneigh p hp
  · apply edges_endpoints_rel Comparable (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro i _
    rw [← finalLabels_trace]
    exact Or.inl (forward_final_le_output g t owner G J H i)

theorem opposite_network_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0)
    (wires : List (Role n a c s)) :
    ∀ p ∈ RankTrace.edges (input g t)
      (networkUpdates wires (output g t) (opposite g t owner G J H)), Comparable p.1 p.2 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact opposite_edges_comparable g t owner G J H target hJ hneigh p hp
  · apply edges_endpoints_rel Comparable (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro i _
    rw [← finalLabels_trace]
    exact Or.inl (opposite_final_le_output g t owner G J H i)

end Comparability

section Loss
variable [FiniteDimensional K E] [FiniteDimensional K F] [Nontrivial R]

/-- No data-X history contributes any actual dimension decrease. -/
theorem forward_x_loss (j : Fin n) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (g.xIn (t j))
      (history (forward (s := s) g t owner G J H) (x j)) = 0 := by
  rw [forward_x_history]
  have h₁ := Submodule.finrank_mono (g.xIn_le_middle (t j))
  have h₂ := Submodule.finrank_mono (g.middle_le_full (t j))
  split_ifs <;> simp [pathLoss] <;> omega

omit [Nontrivial R] in
theorem forward_y_loss (j : Fin n) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (g.yIn (t j))
      (history (forward (s := s) g t owner G J H) (y j)) = 0 := by
  rw [forward_y_history]
  have h₁ := Submodule.finrank_mono (g.yIn_le_common (t j))
  have h₂ := Submodule.finrank_mono (g.common_le_yOut (t j))
  simp [pathLoss]; omega

theorem forward_side_loss (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0) (p : Fin a) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (forward (s := s) g t owner G J H) (side p)) = 0 := by
  rw [forward_side_history g t owner G J H target hJ]
  have h₁ := Submodule.finrank_mono ((g.yIn_le_common (t (target p))).trans
    (show g.common ≤ g.xMiddle (t (owner p)) from le_sup_left))
  have h₂ := Submodule.finrank_mono (g.side_middle_le_out _ _ (hneigh p))
  have h₃ := Submodule.finrank_mono (g.yOut_le_full (t (target p)))
  simp [pathLoss]; omega

omit [Nontrivial R] in
/-- Only the full-to-common transition on a covered central wire loses rank. -/
theorem forward_center_loss (j : Fin c) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (forward (s := s) g t owner G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [forward_center_history]
  have h₁ := Submodule.finrank_mono g.common_le_full
  have h₂ := g.central_dimension_loss
  split_ifs <;> simp [pathLoss]
  omega

theorem inverse_x_loss (j : Fin n) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (g.yIn (t j))
      (history (inverse (s := s) g t owner G J H) (x j)) = 0 := by
  rw [inverse_x_history]
  have h₁ := Submodule.finrank_mono (g.yIn_le_common (t j))
  have h₂ := Submodule.finrank_mono (g.common_le_yOut (t j))
  split_ifs <;> simp [pathLoss] <;> omega

omit [Nontrivial R] in
theorem inverse_y_loss (j : Fin n) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (g.xIn (t j))
      (history (inverse (s := s) g t owner G J H) (y j)) = 0 := by
  rw [inverse_y_history]
  have h₁ := Submodule.finrank_mono (g.xIn_le_middle (t j))
  have h₂ := Submodule.finrank_mono (g.middle_le_full (t j))
  simp [pathLoss]; omega

theorem inverse_side_loss (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0) (p : Fin a) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (inverse (s := s) g t owner G J H) (side p)) = 0 := by
  rw [inverse_side_history g t owner G J H target hJ]
  have h₁ := Submodule.finrank_mono ((g.yIn_le_common (t (owner p))).trans
    (show g.common ≤ g.xMiddle (t (target p)) from le_sup_left))
  have h₂ := Submodule.finrank_mono (g.side_middle_le_out _ _ (hneigh p))
  have h₃ := Submodule.finrank_mono (g.yOut_le_full (t (owner p)))
  simp [pathLoss]; omega

omit [Nontrivial R] in
theorem inverse_center_loss (j : Fin c) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (inverse (s := s) g t owner G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [inverse_center_history]
  have h₁ := Submodule.finrank_mono g.common_le_full
  have h₂ := g.central_dimension_loss
  split_ifs <;> simp [pathLoss]
  omega

/-- The exact forward invocation loss is determined solely by the covered
central columns. All data, side, and spectator histories contribute zero. -/
theorem forward_loss (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (forward g t owner G J H)) =
      ∑ j : Fin c, if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [loss_history]
  simp only [Fintype.sum_sum_type]
  have hx := forward_x_loss (s := s) g t owner G J H
  have hy := forward_y_loss (s := s) g t owner G J H
  have hp := forward_side_loss (s := s) g t owner G J H target hJ hneigh
  have hc := forward_center_loss (s := s) g t owner G J H
  have hs := forward_spectator_history (s := s) g t owner G J H
  simp only [x] at hx
  simp only [y] at hy
  simp only [side] at hp
  simp only [center] at hc
  simp only [spectator] at hs
  simp only [input, hx, hy, hp, hc, hs, pathLoss, Finset.sum_const_zero, zero_add, add_zero]

theorem inverse_loss (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t owner G J H)) =
      ∑ j : Fin c, if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [loss_history]
  simp only [Fintype.sum_sum_type]
  have hx := inverse_x_loss (s := s) g t owner G J H
  have hy := inverse_y_loss (s := s) g t owner G J H
  have hp := inverse_side_loss (s := s) g t owner G J H target hJ hneigh
  have hc := inverse_center_loss (s := s) g t owner G J H
  have hs := inverse_spectator_history (s := s) g t owner G J H
  simp only [x] at hx
  simp only [y] at hy
  simp only [side] at hp
  simp only [center] at hc
  simp only [spectator] at hs
  simp only [inverseInput, hx, hy, hp, hc, hs, pathLoss, Finset.sum_const_zero, zero_add, add_zero]

theorem forward_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (owner p)) (t (target p)) = 0) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (forward g t owner G J H)) ≤
      c * finrank K F := by
  rw [forward_loss g t owner G J H target hJ hneigh]
  calc
    _ ≤ ∑ _j : Fin c, finrank K F := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

theorem inverse_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t owner G J H)) ≤
      c * finrank K F := by
  rw [inverse_loss g t owner G J H target hJ hneigh]
  calc
    _ ≤ ∑ _j : Fin c, finrank K F := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

omit [FiniteDimensional K E] [FiniteDimensional K F] [Nontrivial R] in
/-- Physical role exchange preserves the exact loss; the source profile is
exchanged along with the inverse schedule. -/
theorem opposite_loss_eq_inverse :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (opposite g t owner G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t owner G J H)) := by
  rw [loss_history, loss_history]
  symm
  apply Fintype.sum_equiv (exchangeRoles n a c s)
  intro i
  rw [opposite_history]
  congr 1
  rcases i with i | i | i <;> rfl

theorem opposite_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, g.current (t (target p)) (t (owner p)) = 0) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (opposite g t owner G J H)) ≤
      c * finrank K F := by
  rw [opposite_loss_eq_inverse]
  exact inverse_loss_le g t owner G J H target hJ hneigh

omit [Nontrivial R] in
/-- Explicit output edges contribute zero additional loss in the forward motif. -/
theorem forward_network_loss (wires : List (Role n a c s)) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (networkUpdates wires (output g t) (forward (s := s) g t owner G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (updates (forward (s := s) g t owner G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ i : Role n a c s, (fun U : Submodule K (E ⊗[K] F) => finrank K U) (RankTrace.finish (input g t) (updates (forward (s := s) g t owner G J H)) i) -
      finrank K (output g t i) = 0 := by
    intro i
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (forward_final_le_output g t owner G J H i))
  simp [hz]

/-- Output completion also contributes zero loss for the actual middle inverse. -/
theorem opposite_network_loss (wires : List (Role n a c s)) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (networkUpdates wires (output g t) (opposite (s := s) g t owner G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (updates (opposite (s := s) g t owner G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ i : Role n a c s, (fun U : Submodule K (E ⊗[K] F) => finrank K U) (RankTrace.finish (input g t) (updates (opposite (s := s) g t owner G J H)) i) -
      finrank K (output g t i) = 0 := by
    intro i
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (opposite_final_le_output g t owner G J H i))
  simp [hz]

end Loss

section Nondegeneracy
variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- Every actual forward group carries a proved nondegenerate tensor label. -/
theorem forward_nondegenerate (ht : ∀ j, g.current (t j) (t j) ≠ 0)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ forward g t owner G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  simp only [forward, List.mem_append, List.mem_ofFn, List.mem_singleton, or_assoc] at hv
  rcases hv with ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩ | rfl | rfl | ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
  · exact g.yIn_nondegenerate _ (ht j)
  · exact g.common_nondegenerate
  · exact g.xMiddle_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · exact g.common_nondegenerate
  · exact g.yOut_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · exact g.full_nondegenerate

theorem inverse_nondegenerate (ht : ∀ j, g.current (t j) (t j) ≠ 0)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ inverse g t owner G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  simp only [inverse, List.mem_append, List.mem_ofFn, List.mem_singleton, or_assoc] at hv
  rcases hv with ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩ | rfl | rfl | ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
  · exact g.yIn_nondegenerate _ (ht j)
  · exact g.common_nondegenerate
  · exact g.xMiddle_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · exact g.common_nondegenerate
  · exact g.yOut_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · exact g.full_nondegenerate

theorem opposite_nondegenerate (ht : ∀ j, g.current (t j) (t j) ≠ 0)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ opposite g t owner G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact inverse_nondegenerate g t owner G J H ht w hw

theorem input_nondegenerate (ht : ∀ j, g.current (t j) (t j) ≠ 0) (i : Role n a c s) :
    (g.pairing.restrict (input g t i)).Nondegenerate := by
  rcases i with j | j | j
  · exact g.xIn_nondegenerate _ (ht j)
  · exact g.yIn_nondegenerate _ (ht j)
  · exact bot_nondegenerate _

theorem output_nondegenerate (ht : ∀ j, g.current (t j) (t j) ≠ 0) (i : Role n a c s) :
    (g.pairing.restrict (output g t i)).Nondegenerate := by
  rcases i with j | j | j
  · exact top_nondegenerate _ g.pairing_nondegenerate
  · exact g.yOut_nondegenerate _ (ht j)
  · exact top_nondegenerate _ g.pairing_nondegenerate

end Nondegeneracy

end Schedules
end IntegerMultBounds.Networks.LabeledMotif
