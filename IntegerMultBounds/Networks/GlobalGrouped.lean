import IntegerMultBounds.Networks.GroupedRouting
import IntegerMultBounds.Networks.GlobalCircuitBits

/-! Actual grouped three-coordinate networks on the existing physical wire
layout. Each invocation uses its own stage-indexed side and central banks.
Injective placement transports the exact sparse group support; groups outside
a local invocation are left untouched. The reversed middle schedule retains
its physical side-wire names, and the full run refines `GlobalCircuit`.
No rank, nested-label, numerical-precision, or tape-cost claim is made here. -/

namespace IntegerMultBounds.Networks.GlobalGrouped

open GroupedCircuit

section Embedding
variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R] [DecidableEq R]

/-- Place a complete group into distinct global wire names. -/
def embedGroup (f : ι ↪ κ) (g : Group ι R) : Group κ R where
  rows := g.rows.map (GlobalCircuit.embedGate f)
  separated := by
    intro row hrow other hother p hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨oldOther, hOldOther, rfl⟩ := List.mem_map.mp hother
    obtain ⟨oldp, hOldp, rfl⟩ := List.mem_map.mp hp
    exact f.injective.ne (g.separated old hold oldOther hOldOther oldp hOldp)

omit [DecidableEq R] in
theorem evaluate_embed (f : ι ↪ κ) (g : Group ι R) (r : κ → R) :
    evaluate (embedGroup f g) r ∘ f = evaluate g (r ∘ f) := by
  change evaluateRows (embedGroup f g).rows r ∘ f = evaluateRows g.rows (r ∘ f)
  rw [← run_rows _ (embedGroup f g).separated, ← run_rows _ g.separated]
  exact GlobalCircuit.embed_run f g.rows r

omit [DecidableEq ι] [DecidableEq R] in
theorem evaluate_embed_outside (f : ι ↪ κ) (g : Group ι R) (r : κ → R)
    (k : κ) (hk : ∀ i, f i ≠ k) : evaluate (embedGroup f g) r k = r k := by
  change evaluateRows (embedGroup f g).rows r k = _
  rw [← run_rows _ (embedGroup f g).separated]
  exact GlobalCircuit.embed_outside f g.rows r k hk

/-- Every sparse physical incidence is the image of an actual local incidence. -/
theorem support_embed (f : ι ↪ κ) (g : Group ι R) :
    support (embedGroup f g) = (support g).image f := by
  ext k
  simp only [mem_support, touched_iff, Finset.mem_image]
  constructor
  · rintro ⟨row, hrow, hk⟩
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    rcases hk with hk | ⟨p, hp, hpk, hpn⟩
    · exact ⟨old.target, ⟨old, hold, Or.inl rfl⟩, hk.symm⟩
    · obtain ⟨oldp, hOldp, rfl⟩ := List.mem_map.mp hp
      exact ⟨oldp.1, ⟨old, hold, Or.inr ⟨oldp, hOldp, rfl, hpn⟩⟩, hpk⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨row, hrow, hi⟩ := hi
    refine ⟨GlobalCircuit.embedGate f row, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
    rcases hi with hi | ⟨p, hp, hpi, hpn⟩
    · exact Or.inl (congrArg f hi)
    · exact Or.inr ⟨(f p.1, p.2), List.mem_map.mpr ⟨p, hp, rfl⟩,
        congrArg f hpi, hpn⟩

theorem support_embed_card (f : ι ↪ κ) (g : Group ι R) :
    (support (embedGroup f g)).card = (support g).card := by
  rw [support_embed, Finset.card_image_of_injective _ f.injective]

def embedGroups (f : ι ↪ κ) (gs : List (Group ι R)) : List (Group κ R) :=
  gs.map (embedGroup f)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq R] in
@[simp] theorem embedGroups_length (f : ι ↪ κ) (gs : List (Group ι R)) :
    (embedGroups f gs).length = gs.length := List.length_map _

omit [DecidableEq R] in
theorem run_embedGroups (f : ι ↪ κ) (gs : List (Group ι R)) (r : κ → R) :
    runGroups (embedGroups f gs) r ∘ f = runGroups gs (r ∘ f) := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [embedGroups, List.map_cons, runGroups] at *
    rw [ih, evaluate_embed]

omit [DecidableEq ι] [DecidableEq R] in
theorem run_embedGroups_outside (f : ι ↪ κ) (gs : List (Group ι R)) (r : κ → R)
    (k : κ) (hk : ∀ i, f i ≠ k) : runGroups (embedGroups f gs) r k = r k := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    simp only [embedGroups, List.map_cons, runGroups] at *
    rw [ih, evaluate_embed_outside f g r k hk]

omit [DecidableEq R] in
/-- Whole-register-file refinement: local equivalence plus preservation outside
the placement, without a surjectivity premise on the embedding. -/
theorem embed_refines (f : ι ↪ κ) (gs : List (Group ι R)) (p : Circuit.Program ι R)
    (h : ∀ r, runGroups gs r = Circuit.run p r) (r : κ → R) :
    runGroups (embedGroups f gs) r = Circuit.run (GlobalCircuit.embed f p) r := by
  have hr := run_embedGroups f gs r
  rw [h, ← GlobalCircuit.embed_run] at hr
  funext k
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i, rfl⟩ := hk
    exact congrFun hr i
  · have hout : ∀ i, f i ≠ k := by simpa using hk
    rw [run_embedGroups_outside f gs r k hout, GlobalCircuit.embed_outside f p r k hout]

theorem incidenceCount_embed (f : ι ↪ κ) (gs : List (Group ι R)) :
    incidenceCount (embedGroups f gs) = incidenceCount gs := by
  simp [incidenceCount, embedGroups, List.map_map, Function.comp_def, support_embed_card]
end Embedding

section Schedule
variable {B A C R : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R]
variable {n a c : ℕ}

/-- Stage one and three use the forward motif; stage two uses the role-renamed
inverse motif, retaining the actual reverse-row order. -/
def localGroups (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    List (Group (Circuit.Role n a c 0) R) :=
  if j = 1 then oppositeGroups owner G J H else dirtyGroups owner G J H

theorem localGroups_refines (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3)
    (r : Circuit.Role n a c 0 → R) :
    runGroups (localGroups owner G J H j) r =
      Circuit.run (GlobalCircuit.localProgram (copyMatrix owner 1) G J H j) r := by
  unfold localGroups GlobalCircuit.localProgram
  split
  · exact oppositeGroups_run owner G J H r
  · exact dirtyGroups_run owner G J H r

/-- The embedding is the existing physical layout, including its side-wire
orientation and its distinct scratch bank for each stage/fixed-coordinate pair. -/
def invocationGroups (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    List (Group (GlobalCircuit.World B A C) R) :=
  embedGroups (GlobalCircuit.localEmbedding eB eA eC j q) (localGroups owner G J H j)

theorem invocationGroups_refines (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B)
    (r : GlobalCircuit.World B A C → R) :
    runGroups (invocationGroups eB eA eC owner G J H j q) r =
      Circuit.run (GlobalCircuit.invocationProgram eB eA eC (copyMatrix owner 1) G J H j q) r :=
  embed_refines _ _ _ (localGroups_refines owner G J H j) r

def partialStage (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (qs : List (B × B)) :
    List (Group (GlobalCircuit.World B A C) R) :=
  qs.flatMap (invocationGroups eB eA eC owner G J H j)

theorem partialStage_refines (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (qs : List (B × B))
    (r : GlobalCircuit.World B A C → R) :
    runGroups (partialStage eB eA eC owner G J H j qs) r =
      Circuit.run (GlobalCircuit.partialStage eB eA eC (copyMatrix owner 1) G J H j qs) r := by
  induction qs generalizing r with
  | nil => rfl
  | cons q qs ih =>
    simp only [partialStage, GlobalCircuit.partialStage, List.flatMap_cons,
      runGroups_append, Circuit.run_append, invocationGroups_refines] at *
    exact ih _

def stage (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    List (Group (GlobalCircuit.World B A C) R) :=
  partialStage eB eA eC owner G J H j (GlobalCircuit.keys eB)

def program (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (GlobalCircuit.World B A C) R) :=
  stage eB eA eC owner G J H 0 ++ stage eB eA eC owner G J H 1 ++
    stage eB eA eC owner G J H 2

/-- Full refinement for arbitrary scalar registers, not just initialized banks. -/
theorem program_refines (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : GlobalCircuit.World B A C → R) :
    runGroups (program eB eA eC owner G J H) r =
      Circuit.run (GlobalCircuit.program eB eA eC (copyMatrix owner 1) G J H) r := by
  simp only [program, runGroups_append, stage, partialStage_refines,
    GlobalCircuit.program, Circuit.run_append, GlobalCircuit.stage]

/-- Flattening the sparse groups gives an actual elementary program with the
same global behavior; grouping need not be assumed as an oracle. -/
theorem compiled_program_refines (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : GlobalCircuit.World B A C → R) :
    Circuit.run (compileGroups (program eB eA eC owner G J H)) r =
      Circuit.run (GlobalCircuit.program eB eA eC (copyMatrix owner 1) G J H) r := by
  rw [compileGroups_run, program_refines]

@[simp] theorem localGroups_length (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    (localGroups owner G J H j).length = 4 * n + 4 := by
  unfold localGroups
  split <;> simp [oppositeGroups, dirtyInverseGroups_length, dirtyGroups_length]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
@[simp] theorem invocationGroups_length (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    (invocationGroups eB eA eC owner G J H j q).length = 4 * n + 4 := by
  simp [invocationGroups]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem partialStage_length (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (qs : List (B × B)) :
    (partialStage eB eA eC owner G J H j qs).length = qs.length * (4 * n + 4) := by
  induction qs with
  | nil => simp [partialStage]
  | cons q qs ih =>
    simp only [partialStage, List.flatMap_cons, List.length_append,
      invocationGroups_length, List.length_cons] at *
    rw [ih]
    ring

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Actual grouped count for all three coordinate stages and all invocation keys. -/
theorem program_length (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (program eB eA eC owner G J H).length = 3 * n ^ 2 * (4 * n + 4) := by
  simp only [program, List.length_append, stage, partialStage_length, GlobalCircuit.keys_length]
  ring

/-- Every placed group has exactly the local sparse support in physical names. -/
theorem invocationGroups_support (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B)
    (g : Group (GlobalCircuit.World B A C) R)
    (hg : g ∈ invocationGroups eB eA eC owner G J H j q) :
    ∃ old ∈ localGroups owner G J H j,
      support g = (support old).image (GlobalCircuit.localEmbedding eB eA eC j q) := by
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  exact ⟨old, hold, support_embed _ old⟩

/-- Exact incidence count is independent of which coordinate stage runs the
forward or opposite inverse motif. -/
theorem localGroups_incidenceCount (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    incidenceCount (localGroups owner G J H j) =
      incidenceCount (dirtyGroups (s := 0) owner G J H) := by
  unfold localGroups
  split
  · simp only [oppositeGroups, incidenceCount_rename, dirtyInverseGroups_incidenceCount]
  · rfl

theorem invocationGroups_incidenceCount (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    incidenceCount (invocationGroups eB eA eC owner G J H j q) =
      incidenceCount (dirtyGroups (s := 0) owner G J H) := by
  rw [invocationGroups, incidenceCount_embed, localGroups_incidenceCount]

theorem partialStage_incidenceCount (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (qs : List (B × B)) :
    incidenceCount (partialStage eB eA eC owner G J H j qs) =
      qs.length * incidenceCount (dirtyGroups (s := 0) owner G J H) := by
  induction qs with
  | nil => simp [partialStage, incidenceCount]
  | cons q qs ih =>
    simp only [partialStage, List.flatMap_cons, incidenceCount_append,
      invocationGroups_incidenceCount, List.length_cons] at *
    rw [ih]
    ring

/-- The global number of sparse group/wire incidences is exactly the local
number times the actual number of physical invocations. -/
theorem program_incidenceCount (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    incidenceCount (program eB eA eC owner G J H) =
      3 * n ^ 2 * incidenceCount (dirtyGroups (s := 0) owner G J H) := by
  simp only [program, incidenceCount_append, stage, partialStage_incidenceCount,
    GlobalCircuit.keys_length]
  ring

/-- Every global group's sparse support comes from one concrete coordinate-line
invocation, with no added scratch sharing or dense zero-source incidences. -/
theorem program_support_origin (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (g : Group (GlobalCircuit.World B A C) R)
    (hg : g ∈ program eB eA eC owner G J H) :
    ∃ (j : Fin 3) (q : B × B) (old : Group (Circuit.Role n a c 0) R),
      old ∈ localGroups owner G J H j ∧
      support g = (support old).image (GlobalCircuit.localEmbedding eB eA eC j q) := by
  have hstage (j : Fin 3) (hj : g ∈ stage eB eA eC owner G J H j) :
      ∃ (q : B × B) (old : Group (Circuit.Role n a c 0) R),
        old ∈ localGroups owner G J H j ∧
        support g = (support old).image (GlobalCircuit.localEmbedding eB eA eC j q) := by
    obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hj
    obtain ⟨old, hold, hs⟩ := invocationGroups_support eB eA eC owner G J H j q g hq
    exact ⟨q, old, hold, hs⟩
  simp only [program, List.mem_append] at hg
  rcases hg with (h0 | h1) | h2
  · exact ⟨0, hstage 0 h0⟩
  · exact ⟨1, hstage 1 h1⟩
  · exact ⟨2, hstage 2 h2⟩
end Schedule

section Motifs
open NeighborCounts

/-- Concrete complex groups use exactly the physical neighboring-pair orientation. -/
def complexProgram {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ ComplexPairs h) :
    List (Group (Wires.ComplexRole h) ℚ) :=
  program eB eA (Equiv.refl (Fin (h + 1)))
    (fun p => (GlobalCircuit.complexLocalPairs eB eA p).val.2)
    (Circuit.complexGather (fun i => (eB i).val))
    (Circuit.complexInject (GlobalCircuit.complexLocalPairs eB eA))
    (Circuit.complexScatter (fun i => (eB i).val))

theorem complexProgram_run {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ ComplexPairs h)
    (X Y : Wires.Address h → ℚ)
    (S : Wires.Invocation h × (ComplexPairs h ⊕ Fin (h + 1)) → ℚ) :
    runGroups (complexProgram eB eA) (GlobalCircuit.contents X Y S) =
      GlobalCircuit.contents (-Y) X S := by
  rw [complexProgram, program_refines]
  exact GlobalCircuit.complexProgram_run eB eA X Y S

/-- Concrete bit groups use the same physical layout as the existing bit network. -/
def bitProgram {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h) :
    List (Group (Wires.BitRole h) (ZMod 2)) :=
  program eB eA (Equiv.refl (Fin h))
    (fun p => (GlobalCircuit.bitLocalPairs eB eA p).val.2)
    (Circuit.bitGather (fun i => (eB i).val))
    (Circuit.bitInject (GlobalCircuit.bitLocalPairs eB eA))
    (Circuit.bitScatter (fun i => (eB i).val))

theorem bitProgram_run {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h)
    (X Y : Wires.Address h → ZMod 2)
    (S : Wires.Invocation h × (BitPairs h ⊕ Fin h) → ZMod 2) :
    runGroups (bitProgram eB eA) (GlobalCircuit.contents X Y S) =
      GlobalCircuit.contents Y X S := by
  rw [bitProgram, program_refines]
  exact GlobalCircuit.bitProgram_run eB eA X Y S

theorem complexProgram_length {h n a : ℕ} (eB : Fin n ≃ Triple h)
    (eA : Fin a ≃ ComplexPairs h) :
    (complexProgram eB eA).length = 3 * n ^ 2 * (4 * n + 4) := program_length _ _ _ _ _ _ _

theorem bitProgram_length {h n a : ℕ} (eB : Fin n ≃ Triple h)
    (eA : Fin a ≃ BitPairs h) :
    (bitProgram eB eA).length = 3 * n ^ 2 * (4 * n + 4) := program_length _ _ _ _ _ _ _
end Motifs

end IntegerMultBounds.Networks.GlobalGrouped
