import IntegerMultBounds.Networks.GroupedCircuit

/-! Inverse grouped motifs and their local three-stage exchange. Register
renaming is performed on each finite group's rows before execution, and its
support is transported exactly. The schedule refines the existing elementary
signed exchange while preserving the true multi-output group boundaries.
Counts here are grouped instruction counts, not tape costs or topology bounds. -/

namespace IntegerMultBounds.Networks.GroupedCircuit

variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R] [DecidableEq R]

/-- Rename physical wire roles in every row, retaining the group boundary. -/
def Group.rename (e : ι ≃ κ) (g : Group ι R) : Group κ R where
  rows := g.rows.map (Circuit.Gate.rename e)
  separated := by
    intro row hrow other hother p hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨oldOther, hOldOther, rfl⟩ := List.mem_map.mp hother
    obtain ⟨oldp, hOldp, rfl⟩ := List.mem_map.mp hp
    exact e.injective.ne (g.separated old hold oldOther hOldOther oldp hOldp)

omit [DecidableEq R] in
theorem evaluate_rename (e : ι ≃ κ) (g : Group ι R) (r : κ → R) :
    evaluate (g.rename e) r ∘ e = evaluate g (r ∘ e) := by
  change evaluateRows (g.rename e).rows r ∘ e = evaluateRows g.rows (r ∘ e)
  rw [← run_rows _ (g.rename e).separated, ← run_rows _ g.separated]
  exact Circuit.run_rename e g.rows r

omit [DecidableEq ι] [DecidableEq κ] in
/-- Renaming preserves exactly the sparse incidences, including coefficient tests. -/
theorem touched_rename (e : ι ≃ κ) (g : Group ι R) (i : ι) :
    e i ∈ touched (g.rename e) ↔ i ∈ touched g := by
  rw [touched_iff, touched_iff]
  constructor
  · rintro ⟨row, hrow, hi⟩
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    refine ⟨old, hold, ?_⟩
    rcases hi with hi | ⟨p, hp, hpi, hpn⟩
    · exact Or.inl (e.injective hi)
    · obtain ⟨oldp, hOldp, rfl⟩ := List.mem_map.mp hp
      exact Or.inr ⟨oldp, hOldp, e.injective hpi, hpn⟩
  · rintro ⟨row, hrow, hi⟩
    refine ⟨row.rename e, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
    rcases hi with hi | ⟨p, hp, hpi, hpn⟩
    · exact Or.inl (congrArg e hi)
    · exact Or.inr ⟨(e p.1, p.2), List.mem_map.mpr ⟨p, hp, rfl⟩,
        congrArg e hpi, hpn⟩

theorem support_rename (e : ι ≃ κ) (g : Group ι R) :
    support (g.rename e) = (support g).image e := by
  ext k
  obtain ⟨i, rfl⟩ := e.surjective k
  simp only [mem_support, touched_rename, Finset.mem_image, e.injective.eq_iff,
    exists_eq_right]

theorem support_rename_card (e : ι ≃ κ) (g : Group ι R) :
    (support (g.rename e)).card = (support g).card := by
  rw [support_rename, Finset.card_image_of_injective _ e.injective]

def renameGroups (e : ι ≃ κ) (gs : List (Group ι R)) : List (Group κ R) :=
  gs.map (Group.rename e)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq R] in
@[simp] theorem renameGroups_length (e : ι ≃ κ) (gs : List (Group ι R)) :
    (renameGroups e gs).length = gs.length := List.length_map _

omit [DecidableEq R] in
theorem runGroups_rename (e : ι ≃ κ) (gs : List (Group ι R)) (r : κ → R) :
    runGroups (renameGroups e gs) r ∘ e = runGroups gs (r ∘ e) := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [renameGroups, List.map_cons, runGroups] at *
    rw [ih, evaluate_rename]

private theorem routing_side_x_sep {n a c s : ℕ} (i : Fin a) (j : Fin n) :
    (Circuit.side i : Circuit.Role n a c s) ≠ Circuit.x j := by simp [Circuit.side, Circuit.x]
private theorem routing_y_side_sep {n a c s : ℕ} (i : Fin n) (j : Fin a) :
    (Circuit.y i : Circuit.Role n a c s) ≠ Circuit.side j := by simp [Circuit.y, Circuit.side]
private theorem routing_y_center_sep {n a c s : ℕ} (i : Fin n) (j : Fin c) :
    (Circuit.y i : Circuit.Role n a c s) ≠ Circuit.center j := by simp [Circuit.y, Circuit.center]
private theorem routing_center_x_sep {n a c s : ℕ} (i : Fin c) (j : Fin n) :
    (Circuit.center i : Circuit.Role n a c s) ≠ Circuit.x j := by simp [Circuit.center, Circuit.x]

/-- Reverse cancellation rows with all coefficient signs negated, retaining
source-owned copy and target-owned injection group boundaries. -/
def dirtyInverseGroups {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Circuit.Role n a c s) R) :=
  copyGroups Circuit.side Circuit.x owner 1 routing_side_x_sep ++
  [matrixGroup Circuit.center Circuit.x G routing_center_x_sep] ++
  faninGroups Circuit.y Circuit.side (-J) routing_y_side_sep ++
  [matrixGroup Circuit.y Circuit.center (-H) routing_y_center_sep] ++
  [matrixGroup Circuit.center Circuit.x (-G) routing_center_x_sep] ++
  copyGroups Circuit.side Circuit.x owner (-1) routing_side_x_sep ++
  [matrixGroup Circuit.y Circuit.center H routing_y_center_sep] ++
  faninGroups Circuit.y Circuit.side J routing_y_side_sep

theorem dirtyInverseGroups_run {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    runGroups (dirtyInverseGroups owner G J H) r =
      Circuit.run (Circuit.dirtyInverse (copyMatrix owner 1) G J H) r := by
  have hm : copyMatrix owner (-1 : R) = -(copyMatrix owner 1) := by
    funext i j
    simp only [copyMatrix, Pi.neg_apply]
    split_ifs <;> simp
  simp only [dirtyInverseGroups, runGroups_append, runGroups,
    Circuit.dirtyInverse, Circuit.run_append]
  simp only [copyGroups_run, faninGroups_run, matrixGroup_evaluate, hm]

theorem dirtyInverseGroups_length {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (dirtyInverseGroups (s := s) owner G J H).length = 4 * n + 4 := by
  simp [dirtyInverseGroups, copyGroups, faninGroups]
  omega

/-- This inverse is verified on every state, without assuming reconstruction. -/
theorem dirtyInverseGroups_run_dirty {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    runGroups (dirtyInverseGroups owner G J H) (runGroups (dirtyGroups owner G J H) r) = r := by
  rw [dirtyInverseGroups_run, dirtyGroups_run]
  exact Circuit.dirtyInverse_run_dirty _ _ _ _ r

/-- The middle inverse schedule is compiled with exchanged data-bank names. -/
def oppositeGroups {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Circuit.Role n a c s) R) :=
  renameGroups (Circuit.exchangeRoles n a c s) (dirtyInverseGroups owner G J H)

theorem oppositeGroups_run {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    runGroups (oppositeGroups owner G J H) r =
      Circuit.run (Circuit.rename (Circuit.exchangeRoles n a c s)
        (Circuit.dirtyInverse (copyMatrix owner 1) G J H)) r := by
  have hr := runGroups_rename (Circuit.exchangeRoles n a c s) (dirtyInverseGroups owner G J H) r
  rw [dirtyInverseGroups_run, ← Circuit.run_rename] at hr
  funext k
  obtain ⟨i, rfl⟩ := (Circuit.exchangeRoles n a c s).surjective k
  exact congrFun hr i

/-- Three local grouped stages, with the two dirty scratch banks shared. -/
def signedExchangeGroups {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Circuit.Role n a c s) R) :=
  dirtyGroups owner G J H ++ oppositeGroups owner G J H ++ dirtyGroups owner G J H

/-- Exact scalar refinement to the previously verified elementary exchange. -/
theorem signedExchangeGroups_refines {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    runGroups (signedExchangeGroups owner G J H) r =
      Circuit.run (Circuit.signedExchangeProgram (copyMatrix owner 1) G J H) r := by
  simp only [signedExchangeGroups, runGroups_append, dirtyGroups_run, oppositeGroups_run,
    Circuit.signedExchangeProgram, Circuit.run_append]

theorem signedExchangeGroups_length {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (signedExchangeGroups (s := s) owner G J H).length = 3 * (4 * n + 4) := by
  simp only [signedExchangeGroups, List.length_append, dirtyGroups_length,
    oppositeGroups, renameGroups_length, dirtyInverseGroups_length]
  omega

/-- The compiled zero-free elementary program implements the same exchange. -/
theorem signedExchangeGroups_compile {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Circuit.Role n a c s → R) :
    Circuit.run (compileGroups (signedExchangeGroups owner G J H)) r =
      Circuit.run (Circuit.signedExchangeProgram (copyMatrix owner 1) G J H) r := by
  rw [compileGroups_run, signedExchangeGroups_refines]

/-- The concrete bit motif swaps both data banks and restores arbitrary dirty
scratch and every spectator. Only physical wire labels/enumeration are inputs. -/
theorem bit_exchangeGroups_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.BitPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin h → ZMod 2) (S : Fin s → ZMod 2) :
    runGroups (signedExchangeGroups (fun p => (e p).val.2) (Circuit.bitGather L)
      (Circuit.bitInject e) (Circuit.bitScatter L)) (Circuit.banks X Y A C S) =
      Circuit.banks Y X A C S := by
  rw [signedExchangeGroups_refines]
  exact Circuit.bit_exchange_run e hinj hcard X Y A C S

/-- The rational motif implements its signed exchange on all banks. -/
theorem complex_exchangeGroups_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ Circuit.ComplexPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ℚ)
    (A : Fin a → ℚ) (C : Fin (h + 1) → ℚ) (S : Fin s → ℚ) :
    runGroups (signedExchangeGroups (fun p => (e p).val.2) (Circuit.complexGather L)
      (Circuit.complexInject e) (Circuit.complexScatter L)) (Circuit.banks X Y A C S) =
      Circuit.banks (-Y) X A C S := by
  rw [signedExchangeGroups_refines]
  exact Circuit.complex_signedExchange_run e hinj hcard X Y A C S

/-- The total number of group/wire incidences, using each group's actual sparse
support set. This is neither a depth nor a running-time measure. -/
def incidenceCount (gs : List (Group ι R)) : ℕ := (gs.map fun g => (support g).card).sum

@[simp] theorem incidenceCount_append (gs hs : List (Group ι R)) :
    incidenceCount (gs ++ hs) = incidenceCount gs + incidenceCount hs := by
  simp [incidenceCount]

theorem incidenceCount_rename (e : ι ≃ κ) (gs : List (Group ι R)) :
    incidenceCount (renameGroups e gs) = incidenceCount gs := by
  simp [incidenceCount, renameGroups, List.map_map, Function.comp_def, support_rename_card]

/-- Inverse and forward motifs have exactly the same total physical incidences;
they reorder the same eight grouped rows. -/
theorem dirtyInverseGroups_incidenceCount {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    incidenceCount (dirtyInverseGroups (s := s) owner G J H) =
      incidenceCount (dirtyGroups (s := s) owner G J H) := by
  simp only [dirtyInverseGroups, dirtyGroups, incidenceCount_append]
  omega

/-- The middle stage transports every support set by the fixed role exchange. -/
theorem oppositeGroups_support {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (g : Group (Circuit.Role n a c s) R) (hg : g ∈ oppositeGroups owner G J H) :
    ∃ old ∈ dirtyInverseGroups (s := s) owner G J H,
      support g = (support old).image (Circuit.exchangeRoles n a c s) := by
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  exact ⟨old, hold, support_rename _ old⟩

/-- Three stages triple incidence count exactly; sparse support is not replaced
by dense zero-coefficient rows in this count. -/
theorem signedExchangeGroups_incidenceCount {n a c s : ℕ} (owner : Fin a → Fin n)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    incidenceCount (signedExchangeGroups (s := s) owner G J H) =
      3 * incidenceCount (dirtyGroups (s := s) owner G J H) := by
  simp only [signedExchangeGroups, incidenceCount_append, oppositeGroups,
    incidenceCount_rename, dirtyInverseGroups_incidenceCount]
  omega

end IntegerMultBounds.Networks.GroupedCircuit
