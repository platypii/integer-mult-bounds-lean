import IntegerMultBounds.Networks.FramedCircuit
import IntegerMultBounds.Networks.CircuitBits

/-! Finite grouped linear updates, with their actual scalar incidences. A group
reads its source registers before simultaneously adding to its destinations.
Disjoint source/destination banks permit refinement to an elementary circuit.
The compiler removes zero-coefficient source terms, and the support theorem
characterizes exactly the remaining target and source incidences. No tape cost
or identification of an elementary instruction with a grouped gate is made. -/

namespace IntegerMultBounds.Networks.GroupedCircuit

open Circuit (Gate)

variable {ι R : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]

/-- Remove formally listed zero coefficients before exposing gate incidences. -/
def sparseGate (g : Gate ι R) : Gate ι R :=
  ⟨g.target, g.terms.filter (fun p => decide (p.2 ≠ 0))⟩

theorem sparseGate_run (g : Gate ι R) (r : ι → R) :
    (sparseGate g).run r = g.run r := by
  have hs (ps : List (ι × R)) :
      ((ps.filter (fun p => decide (p.2 ≠ 0))).map fun p => p.2 * r p.1).sum =
        (ps.map fun p => p.2 * r p.1).sum := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.filter_cons]
      split
      · simp only [List.map_cons, List.sum_cons, ih]
      · rename_i hz
        have hp : p.2 = 0 := by simpa using hz
        simp only [List.map_cons, List.sum_cons, hp, zero_mul, zero_add, ih]
  simp only [Gate.run, sparseGate, hs]

omit [DecidableEq ι] in
theorem sparseGate_touched (g : Gate ι R) (i : ι) :
    i ∈ FramedCircuit.touched (sparseGate g) ↔
      i = g.target ∨ ∃ p ∈ g.terms, p.1 = i ∧ p.2 ≠ 0 := by
  simp only [FramedCircuit.touched, sparseGate, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  aesop

omit [DecidableEq ι] in
theorem sparseGate_nonzero (g : Gate ι R) (p : ι × R) (hp : p ∈ (sparseGate g).terms) :
    p.2 ≠ 0 := by simpa [sparseGate] using (List.mem_filter.mp hp).2

/-- Sources in every row are disjoint from all destinations in the same group.
Repeated destinations are harmless: their simultaneous increments are summed. -/
def Separated (rows : List (Gate ι R)) : Prop :=
  ∀ g ∈ rows, ∀ h ∈ rows, ∀ p ∈ h.terms, p.1 ≠ g.target

/-- One grouped multi-output gate with a proved read/write separation. -/
structure Group (ι R : Type*) [CommRing R] where
  rows : List (Gate ι R)
  separated : Separated rows

/-- Every row reads the original register state, including repeated targets. -/
def evaluateRows (rows : List (Gate ι R)) (r : ι → R) : ι → R :=
  fun i => r i + (rows.map fun g => if g.target = i then
    (g.terms.map fun p => p.2 * r p.1).sum else 0).sum

def evaluate (g : Group ι R) (r : ι → R) : ι → R := evaluateRows g.rows r

/-- Compiling a group is finite and retains its declared group boundary. -/
def compile (g : Group ι R) : Circuit.Program ι R := g.rows.map sparseGate

/-- The exact list of incidences after removing zero coefficients. Duplicates
remain explicit incidences, as in the elementary common-frame compiler. -/
def touched (g : Group ι R) : List ι :=
  (compile g).flatMap FramedCircuit.touched

/-- The finite set of physical wire roles incident to the group. -/
def support (g : Group ι R) : Finset ι := (touched g).toFinset

@[simp] theorem mem_support (g : Group ι R) (i : ι) :
    i ∈ support g ↔ i ∈ touched g := List.mem_toFinset

private theorem run_sparse_rows (rows : List (Gate ι R)) (r : ι → R) :
    Circuit.run (rows.map sparseGate) r = Circuit.run rows r := by
  induction rows generalizing r with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, Circuit.run_cons, sparseGate_run, ih]

omit [DecidableEq R] in
/-- A separated elementary schedule agrees with the simultaneous linear update. -/
theorem run_rows (rows : List (Gate ι R)) (sep : Separated rows) (r : ι → R) :
    Circuit.run rows r = evaluateRows rows r := by
  induction rows generalizing r with
  | nil => funext i; simp [Circuit.run, evaluateRows]
  | cons g gs ih =>
    have htail : Separated gs := fun a ha b hb p hp => sep a (by simp [ha]) b (by simp [hb]) p hp
    have hread (h : Gate ι R) (hh : h ∈ gs) (p : ι × R) (hp : p ∈ h.terms) :
        g.run r p.1 = r p.1 := by
      exact Function.update_of_ne (sep g (by simp) h (by simp [hh]) p hp) _ _
    have hs (h : Gate ι R) (hh : h ∈ gs) :
        (h.terms.map fun p => p.2 * g.run r p.1).sum =
          (h.terms.map fun p => p.2 * r p.1).sum := by
      congr 1
      apply List.map_congr_left
      intro p hp
      rw [hread h hh p hp]
    funext i
    rw [Circuit.run_cons, ih htail]
    simp only [evaluateRows, List.map_cons, List.sum_cons]
    have hs' : (gs.map fun h => if h.target = i then
        (h.terms.map fun p => p.2 * g.run r p.1).sum else 0).sum =
        (gs.map fun h => if h.target = i then
        (h.terms.map fun p => p.2 * r p.1).sum else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro h hh
      rw [hs h hh]
    rw [hs']
    by_cases hi : g.target = i
    · subst i
      simp [Gate.run, add_assoc]
    · simp [Gate.run, Function.update_of_ne (Ne.symm hi), hi]

/-- Scalar refinement of a grouped gate to its zero-free elementary schedule. -/
theorem compile_run (g : Group ι R) (r : ι → R) :
    Circuit.run (compile g) r = evaluate g r := by
  rw [compile, run_sparse_rows, run_rows _ g.separated]
  rfl

omit [DecidableEq ι] in
/-- Exact grouped support: all declared output rows, and only nonzero sources. -/
theorem touched_iff (g : Group ι R) (i : ι) :
    i ∈ touched g ↔ ∃ row ∈ g.rows,
      i = row.target ∨ ∃ p ∈ row.terms, p.1 = i ∧ p.2 ≠ 0 := by
  simp only [touched, compile, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨row, ⟨old, hold, rfl⟩, hi⟩
    exact ⟨old, hold, (sparseGate_touched old i).mp hi⟩
  · rintro ⟨row, hrow, hi⟩
    exact ⟨sparseGate row, ⟨row, hrow, rfl⟩, (sparseGate_touched row i).mpr hi⟩

/-- A wire outside the target rows is preserved, even if it is a nonzero source. -/
theorem evaluate_preserves (g : Group ι R) (r : ι → R) (i : ι)
    (hi : ∀ row ∈ g.rows, row.target ≠ i) : evaluate g r i = r i := by
  rw [← compile_run]
  apply Circuit.run_preserves
  intro row hrow
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
  exact hi old hold

/-- An ordinary disjoint-bank matrix addition as one simultaneous grouped gate. -/
def matrixGroup {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) : Group ι R where
  rows := Circuit.block dst src M
  separated := by
    intro g hg h hh p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hh
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
    exact (sep i k).symm

theorem matrixGroup_run {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) (r : ι → R) (k : ι) :
    evaluate (matrixGroup dst src M sep) r k =
      r k + ∑ i, if dst i = k then ∑ j, M i j * r (src j) else 0 := by
  rw [← compile_run, compile, run_sparse_rows]
  change Circuit.run (Circuit.block dst src M) r k = _
  exact Circuit.block_run dst src M sep r k

omit [DecidableEq ι] in
/-- Exact matrix-group support; zero coefficients contribute no source incidence. -/
theorem matrixGroup_touched {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) (k : ι) :
    k ∈ touched (matrixGroup dst src M sep) ↔
      (∃ i, k = dst i) ∨ (∃ i j, src j = k ∧ M i j ≠ 0) := by
  rw [touched_iff]
  constructor
  · rintro ⟨row, hrow, hi⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    rcases hi with hi | ⟨p, hp, hpk, hpn⟩
    · exact Or.inl ⟨i, hi⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
      exact Or.inr ⟨i, j, hpk, hpn⟩
  · have hrow (i : Fin n) : Circuit.rowGate dst src M i ∈
        (matrixGroup dst src M sep).rows :=
      List.mem_map.mpr ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
    rintro (⟨i, hi⟩ | ⟨i, j, hj⟩)
    · exact ⟨_, hrow i, Or.inl hi⟩
    · exact ⟨_, hrow i, Or.inr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩⟩

/-- One source feeds only the destination wires with nonzero coefficients.
Unlike a full matrix row expansion, zero outputs do not become incidences. -/
def fanoutGroup {n : ℕ} (dst : Fin n → ι) (src : ι) (coeff : Fin n → R)
    (sep : ∀ i, dst i ≠ src) : Group ι R where
  rows := ((List.ofFn fun i : Fin n => i).filter (fun i => decide (coeff i ≠ 0))).map
    (fun i => ⟨dst i, [(src, coeff i)]⟩)
  separated := by
    intro g hg h hh p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hh
    have hp' : p = (src, coeff j) := List.mem_singleton.mp hp
    subst p
    exact (sep i).symm

/-- The sparse multi-output fanout still applies the complete coefficient vector. -/
theorem fanoutGroup_run {n : ℕ} (dst : Fin n → ι) (src : ι) (coeff : Fin n → R)
    (sep : ∀ i, dst i ≠ src) (r : ι → R) (k : ι) :
    evaluate (fanoutGroup dst src coeff sep) r k =
      r k + ∑ i, if dst i = k then coeff i * r src else 0 := by
  have hf (is : List (Fin n)) :
      ((is.filter (fun i => decide (coeff i ≠ 0))).map
        (fun i => if dst i = k then coeff i * r src else 0)).sum =
      (is.map (fun i => if dst i = k then coeff i * r src else 0)).sum := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.filter_cons]
      split
      · simp only [List.map_cons, List.sum_cons, ih]
      · rename_i hz
        have hc : coeff i = 0 := by simpa using hz
        simp only [List.map_cons, List.sum_cons, hc, zero_mul, ite_self, zero_add, ih]
  simp only [evaluate, evaluateRows, fanoutGroup, List.map_map, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
  rw [hf]
  simp [List.map_ofFn, List.sum_ofFn]

omit [DecidableEq ι] in
/-- No unconnected destination or zero-only source appears in a sparse fanout. -/
theorem fanoutGroup_touched {n : ℕ} (dst : Fin n → ι) (src : ι) (coeff : Fin n → R)
    (sep : ∀ i, dst i ≠ src) (k : ι) :
    k ∈ touched (fanoutGroup dst src coeff sep) ↔
      (∃ i, coeff i ≠ 0 ∧ k = dst i) ∨ (k = src ∧ ∃ i, coeff i ≠ 0) := by
  rw [touched_iff]
  constructor
  · rintro ⟨row, hrow, hk⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hc : coeff i ≠ 0 := by simpa using (List.mem_filter.mp hi).2
    rcases hk with hk | ⟨p, hp, hpk, _⟩
    · exact Or.inl ⟨i, hc, hk⟩
    · have hp' : p = (src, coeff i) := List.mem_singleton.mp hp
      subst p
      exact Or.inr ⟨hpk.symm, i, hc⟩
  · have hrow (i : Fin n) (hc : coeff i ≠ 0) :
        (⟨dst i, [(src, coeff i)]⟩ : Gate ι R) ∈ (fanoutGroup dst src coeff sep).rows := by
      apply List.mem_map.mpr
      exact ⟨i, List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa⟩, rfl⟩
    rintro (⟨i, hc, hk⟩ | ⟨hk, i, hc⟩)
    · exact ⟨_, hrow i hc, Or.inl hk⟩
    · exact ⟨_, hrow i hc, Or.inr ⟨(src, coeff i), by simp, hk.symm, hc⟩⟩

/-- One destination receives a sparse linear combination of a disjoint source bank. -/
def faninGroup {n : ℕ} (dst : ι) (src : Fin n → ι) (coeff : Fin n → R)
    (sep : ∀ i, dst ≠ src i) : Group ι R :=
  matrixGroup (fun _ : Fin 1 => dst) src (fun _ => coeff) (fun _ => sep)

theorem faninGroup_run {n : ℕ} (dst : ι) (src : Fin n → ι) (coeff : Fin n → R)
    (sep : ∀ i, dst ≠ src i) (r : ι → R) (k : ι) :
    evaluate (faninGroup dst src coeff sep) r k =
      r k + if dst = k then ∑ i, coeff i * r (src i) else 0 := by
  simpa [faninGroup] using matrixGroup_run (fun _ : Fin 1 => dst) src
    (fun _ => coeff) (fun _ => sep) r k

omit [DecidableEq ι] in
theorem faninGroup_touched {n : ℕ} (dst : ι) (src : Fin n → ι) (coeff : Fin n → R)
    (sep : ∀ i, dst ≠ src i) (k : ι) :
    k ∈ touched (faninGroup dst src coeff sep) ↔
      k = dst ∨ ∃ i, src i = k ∧ coeff i ≠ 0 := by
  simpa [faninGroup] using matrixGroup_touched (fun _ : Fin 1 => dst) src
    (fun _ => coeff) (fun _ => sep) k

/-- Source-owned copy or undo group: one data source and exactly its neighboring
side wires. `owner` can be either bit or complex motif's pair-source projection. -/
def copyGroup {n a : ℕ} (dst : Fin a → ι) (src : Fin n → ι) (owner : Fin a → Fin n)
    (c : R) (sep : ∀ i j, dst i ≠ src j) (j : Fin n) : Group ι R :=
  fanoutGroup dst (src j) (fun i => if owner i = j then c else 0) (fun i => sep i j)

omit [DecidableEq ι] in
theorem copyGroup_touched {n a : ℕ} (dst : Fin a → ι) (src : Fin n → ι)
    (owner : Fin a → Fin n) (c : R) (hc : c ≠ 0) (sep : ∀ i j, dst i ≠ src j)
    (j : Fin n) (k : ι) :
    k ∈ touched (copyGroup dst src owner c sep j) ↔
      (∃ i, owner i = j ∧ k = dst i) ∨ (k = src j ∧ ∃ i, owner i = j) := by
  rw [copyGroup, fanoutGroup_touched]
  simp [hc]

/-- A finite grouped schedule retains its boundaries in its denotational run. -/
def runGroups : List (Group ι R) → (ι → R) → (ι → R)
  | [], r => r
  | g :: gs, r => runGroups gs (evaluate g r)

def compileGroups (gs : List (Group ι R)) : Circuit.Program ι R := gs.flatMap compile

theorem compileGroups_run (gs : List (Group ι R)) (r : ι → R) :
    Circuit.run (compileGroups gs) r = runGroups gs r := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [compileGroups, List.flatMap_cons, Circuit.run_append, compile_run,
      runGroups] at *
    exact ih _


omit [DecidableEq R] in
theorem runGroups_append (gs hs : List (Group ι R)) (r : ι → R) :
    runGroups (gs ++ hs) r = runGroups hs (runGroups gs r) := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih => exact ih _

def copyMatrix {n a : ℕ} (owner : Fin a → Fin n) (c : R) : Fin a → Fin n → R :=
  fun i j => if owner i = j then c else 0

/-- One grouped fanout per source, rather than one elementary row per side wire. -/
def copyGroups {n a : ℕ} (dst : Fin a → ι) (src : Fin n → ι) (owner : Fin a → Fin n)
    (c : R) (sep : ∀ i j, dst i ≠ src j) : List (Group ι R) :=
  (List.ofFn fun j : Fin n => j).map (copyGroup dst src owner c sep)

private theorem copyRows_run {n a : ℕ} (dst : Fin a → ι) (src : Fin n → ι)
    (owner : Fin a → Fin n) (c : R) (sep : ∀ i j, dst i ≠ src j)
    (js : List (Fin n)) (r : ι → R) (k : ι) :
    runGroups (js.map (copyGroup dst src owner c sep)) r k =
      r k + (js.map fun j => ∑ i, if dst i = k then
        copyMatrix owner c i j * r (src j) else 0).sum := by
  induction js generalizing r with
  | nil => simp [runGroups]
  | cons j js ih =>
    have hs (t : Fin n) : evaluate (copyGroup dst src owner c sep j) r (src t) = r (src t) := by
      rw [copyGroup, fanoutGroup_run]
      simp [sep]
    rw [List.map_cons, runGroups, ih]
    simp_rw [hs]
    rw [copyGroup, fanoutGroup_run]
    simp only [List.map_cons, List.sum_cons, copyMatrix, add_assoc]

/-- Regrouping copies by their source has exactly the original matrix semantics. -/
theorem copyGroups_run {n a : ℕ} (dst : Fin a → ι) (src : Fin n → ι)
    (owner : Fin a → Fin n) (c : R) (sep : ∀ i j, dst i ≠ src j) (r : ι → R) :
    runGroups (copyGroups dst src owner c sep) r =
      Circuit.run (Circuit.block dst src (copyMatrix owner c)) r := by
  funext k
  rw [copyGroups, copyRows_run, Circuit.block_run dst src _ sep]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : dst i = k <;> simp [hi]

/-- One grouped sparse injection per target. -/
def faninGroups {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) : List (Group ι R) :=
  (List.ofFn fun i : Fin n => i).map (fun i => faninGroup (dst i) src (M i) (sep i))

private theorem faninGroup_evaluate {m : ℕ} (dst : ι) (src : Fin m → ι)
    (coeff : Fin m → R) (sep : ∀ i, dst ≠ src i) (r : ι → R) :
    evaluate (faninGroup dst src coeff sep) r =
      (⟨dst, List.ofFn fun j => (src j, coeff j)⟩ : Gate ι R).run r := by
  funext k
  rw [faninGroup_run]
  by_cases hk : dst = k
  · subst k
    simp [Gate.run, List.map_ofFn, List.sum_ofFn]
  · simp [Gate.run, hk, Function.update_of_ne (Ne.symm hk)]

/-- Splitting the matrix into target-owned injection groups preserves its run. -/
theorem faninGroups_run {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) (r : ι → R) :
    runGroups (faninGroups dst src M sep) r = Circuit.run (Circuit.block dst src M) r := by
  unfold faninGroups Circuit.block
  generalize (List.ofFn fun i : Fin n => i) = is
  induction is generalizing r with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, runGroups, Circuit.run_cons, faninGroup_evaluate]
    exact ih _

/-- A central multi-output matrix is one group, not a collection of group boundaries. -/
theorem matrixGroup_evaluate {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (sep : ∀ i j, dst i ≠ src j) (r : ι → R) :
    evaluate (matrixGroup dst src M sep) r = Circuit.run (Circuit.block dst src M) r := by
  rw [← compile_run, compile, run_sparse_rows]
  rfl

private theorem side_x_sep {n a c s : ℕ} (i : Fin a) (j : Fin n) :
    (Circuit.side i : Circuit.Role n a c s) ≠ Circuit.x j := by simp [Circuit.side, Circuit.x]

private theorem y_side_sep {n a c s : ℕ} (i : Fin n) (j : Fin a) :
    (Circuit.y i : Circuit.Role n a c s) ≠ Circuit.side j := by simp [Circuit.y, Circuit.side]

private theorem y_center_sep {n a c s : ℕ} (i : Fin n) (j : Fin c) :
    (Circuit.y i : Circuit.Role n a c s) ≠ Circuit.center j := by simp [Circuit.y, Circuit.center]

private theorem center_x_sep {n a c s : ℕ} (i : Fin c) (j : Fin n) :
    (Circuit.center i : Circuit.Role n a c s) ≠ Circuit.x j := by simp [Circuit.center, Circuit.x]

/-- The manuscript's eight rows with their true group boundaries: side injection
has one group per target, side copy/undo one group per source, and each central
matrix row of the schedule is a single multi-output group. -/
def dirtyGroups {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Circuit.Role n a c s) R) :=
  faninGroups Circuit.y Circuit.side (-J) y_side_sep ++
  [matrixGroup Circuit.y Circuit.center (-H) y_center_sep] ++
  copyGroups Circuit.side Circuit.x owner 1 side_x_sep ++
  [matrixGroup Circuit.center Circuit.x G center_x_sep] ++
  [matrixGroup Circuit.y Circuit.center H y_center_sep] ++
  faninGroups Circuit.y Circuit.side J y_side_sep ++
  [matrixGroup Circuit.center Circuit.x (-G) center_x_sep] ++
  copyGroups Circuit.side Circuit.x owner (-1) side_x_sep

/-- Number of grouped gates in the eight-row schedule, before any tape
compilation. Empty fanouts are still represented by their declared group. -/
theorem dirtyGroups_length {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (dirtyGroups (s := s) owner G J H).length = 4 * n + 4 := by
  simp [dirtyGroups, copyGroups, faninGroups]
  omega

/-- Sparse regrouping refines to the previously proved complete dirty schedule. -/
theorem dirtyGroups_run {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    runGroups (dirtyGroups owner G J H) r =
      Circuit.run (Circuit.dirty (copyMatrix owner 1) G J H) r := by
  have hm : copyMatrix owner (-1 : R) = -(copyMatrix owner 1) := by
    funext i j
    simp only [copyMatrix, Pi.neg_apply]
    split_ifs <;> simp
  simp only [dirtyGroups, runGroups_append, runGroups, Circuit.dirty, Circuit.run_append]
  simp only [copyGroups_run, faninGroups_run, matrixGroup_evaluate, hm]

/-- Instantiation by the concrete bit motif, with dirty banks and spectators
restored; no sparse-support or reconstruction premise is assumed. -/
theorem bit_dirtyGroups_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.BitPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin h → ZMod 2) (S : Fin s → ZMod 2) :
    runGroups (dirtyGroups (fun p => (e p).val.2) (Circuit.bitGather L)
      (Circuit.bitInject e) (Circuit.bitScatter L)) (Circuit.banks X Y A C S) =
      Circuit.banks X (Y + X) A C S := by
  rw [dirtyGroups_run]
  exact Circuit.bit_dirty_run e hinj hcard X Y A C S

/-- The rational complex motif has the same source-owned copy grouping. -/
theorem complex_dirtyGroups_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ℚ)
    (A : Fin a → ℚ) (C : Fin (h + 1) → ℚ) (S : Fin s → ℚ) :
    runGroups (dirtyGroups (fun p => (e p).val.2) (Circuit.complexGather L)
      (Circuit.complexInject e) (Circuit.complexScatter L)) (Circuit.banks X Y A C S) =
      Circuit.banks X (Y + X) A C S := by
  rw [dirtyGroups_run]
  exact Circuit.complex_dirty_run e hinj hcard X Y A C S

section Frames
variable {E : Type*} [AddCommGroup E] [Module R E]

omit [DecidableEq R] in
private theorem run_gateInstructions (rows : List (Gate ι R)) (r : ι → E) :
    FramedCircuit.run (rows.map FramedCircuit.Instruction.gate) r =
      FramedCircuit.moduleRun rows r := by
  induction rows generalizing r with
  | nil => rfl
  | cons row rows ih => exact ih _

omit [DecidableEq R] in
private theorem moduleRun_common (rows : List (Gate ι R))
    (current : ι → FramedCircuit.Frame R E) (D : FramedCircuit.Frame R E)
    (h : ∀ row ∈ rows, ∀ i ∈ FramedCircuit.touched row, current i = D) (r : ι → E) :
    FramedCircuit.moduleRun rows (FramedCircuit.encode current r) =
      FramedCircuit.encode current (FramedCircuit.moduleRun rows r) := by
  induction rows generalizing r with
  | nil => rfl
  | cons row rows ih =>
    rw [FramedCircuit.moduleRun_cons,
      FramedCircuit.gate_invariant row current D (h row (by simp))]
    exact ih (fun g hg => h g (by simp [hg])) _

/-- Align all actual incidences once, then run the compiled rows in one common
frame. This retains the multi-output group boundary explicitly. -/
def compileFramed (g : Group ι R) (current : ι → FramedCircuit.Frame R E)
    (D : FramedCircuit.Frame R E) : List (FramedCircuit.Instruction ι R E) :=
  FramedCircuit.edges current (fun _ => D) (touched g) ++
    (compile g).map FramedCircuit.Instruction.gate

theorem compileFramed_invariant (g : Group ι R) (current : ι → FramedCircuit.Frame R E)
    (D : FramedCircuit.Frame R E) (r : ι → E) :
    FramedCircuit.run (compileFramed g current D) (FramedCircuit.encode current r) =
      FramedCircuit.encode (FramedCircuit.afterEdges current (fun _ => D) (touched g))
        (FramedCircuit.moduleRun (compile g) r) := by
  rw [compileFramed, FramedCircuit.run_append, FramedCircuit.edges_invariant,
    run_gateInstructions]
  apply moduleRun_common _ _ D
  intro row hrow i hi
  have ht : i ∈ touched g := List.mem_flatMap.mpr ⟨row, hrow, hi⟩
  simp [FramedCircuit.afterEdges_apply, ht]
end Frames

/-- At every array address the grouped framed circuit implements the original
simultaneous scalar update, under the new profile on its exact support. -/
theorem compileFramed_pointwise {Ω : Type*} (g : Group ι R)
    (current : ι → FramedCircuit.Frame R (Ω → R)) (D : FramedCircuit.Frame R (Ω → R))
    (r : ι → Ω → R) :
    FramedCircuit.run (compileFramed g current D) (FramedCircuit.encode current r) =
      FramedCircuit.encode (FramedCircuit.afterEdges current (fun _ => D) (touched g))
        (fun i ω => evaluate g (fun j => r j ω) i) := by
  rw [compileFramed_invariant]
  congr 1
  funext i ω
  rw [FramedCircuit.moduleRun_pointwise, compile_run]

end IntegerMultBounds.Networks.GroupedCircuit
