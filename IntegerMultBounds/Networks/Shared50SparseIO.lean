import IntegerMultBounds.Networks.Shared50Dirty
import IntegerMultBounds.Networks.DAGSourceRoles
import IntegerMultBounds.Networks.SparseCircuit

/-! Actual sparse input/output instructions for the shared fifty-point program.
Every update is a one-source XOR, and all destinations are actual physical
source roles or requested data outputs. No dense zero terms are emitted. -/

namespace IntegerMultBounds.Networks.Shared50SparseIO

open DisjointCircuit NeighborCounts SharedPointReplay Circuit

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50Finite.output Shared50Dirty.pairIndex Shared50Dirty.partialRole

private theorem bank_load_run {n s : ℕ} (entries : List (Fin s × Fin n))
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies DirtyLinearCircuit.scratch DirtyLinearCircuit.x entries)
      (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X Y
        (S + fun i => (entries.map (fun entry => if entry.1 = i then X entry.2 else 0)).sum) := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [DirtyLinearCircuit.scratch, DirtyLinearCircuit.x])]
  rcases role with i | i | i
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch, DirtyLinearCircuit.x]

private theorem bank_read_run {n s : ℕ} (entries : List (Fin n × Fin s))
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies DirtyLinearCircuit.y DirtyLinearCircuit.scratch entries)
      (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X
        (Y + fun i => (entries.map (fun entry => if entry.1 = i then S entry.2 else 0)).sum) S := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [DirtyLinearCircuit.y, DirtyLinearCircuit.scratch])]
  rcases role with i | i | i
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y]

abbrev Source := {entry : ℕ × ℕ // entry ∈ SharedPointExecution.code.sources}

private theorem source_mem_compile (entry : Source) :
    entry.val ∈ (DAGAllocator.compile circuit.nodes outputRefs).sources := by
  simpa only [SharedPointExecution.code] using entry.property

/-- The allocator's physical source slot, with its actual finite bound. -/
def sourceRole (entry : Source) : Fin 509194 :=
  ⟨entry.val.2, (DAGSourceRoles.sources_bound circuit.nodes outputRefs entry.val (source_mem_compile entry)).trans_le
    (by simpa only [SharedPointExecution.code] using Shared50Certificate.role_bound)⟩

/-- The semantic input label of this particular physical source occurrence. -/
def sourceLabel (entry : Source) : Triple 50 :=
  DAGSourceRoles.label circuit.nodes outputRefs entry.val (source_mem_compile entry)

/-- Distinct source entries occupy distinct physical slots, even if their
semantic input labels coincide. -/
theorem sourceRole_injective : Function.Injective sourceRole := by
  intro a b he
  have hn : (SharedPointExecution.code.sources.map Prod.snd).Nodup := by
    simpa only [SharedPointExecution.code] using
      DAGValueTransfer.compile_sources_nodup circuit.nodes outputRefs
  apply Subtype.ext
  exact List.inj_on_of_nodup_map hn a.property b.property (congrArg Fin.val he)

theorem source_roles_nodup : (SharedPointExecution.code.sources.attach.map sourceRole).Nodup := by
  have hn : (SharedPointExecution.code.sources.map Prod.snd).Nodup := by
    simpa only [SharedPointExecution.code] using
      DAGValueTransfer.compile_sources_nodup circuit.nodes outputRefs
  exact List.Nodup.map sourceRole_injective (List.nodup_attach.mpr (List.Nodup.of_map _ hn))

section Lists
variable {n : ℕ}

/-- Exactly one copy for every actual allocator source entry. -/
def sourceEntries (e : Fin n ≃ Triple 50) : List (Fin 509194 × Fin n) :=
  SharedPointExecution.code.sources.attach.map (fun entry => (sourceRole entry, e.symm (sourceLabel entry)))

def load (e : Fin n ≃ Triple 50) : Program (DirtyLinearCircuit.Register n 509194) (ZMod 2) :=
  SparseCircuit.copies DirtyLinearCircuit.scratch DirtyLinearCircuit.x (sourceEntries e)

/-- All three common-point outputs of each target are read, in a fixed finite order. -/
def readEntries (e : Fin n ≃ Triple 50) : List (Fin n × Fin 509194) :=
  (List.ofFn (fun i : Fin n => i)).flatMap (fun i =>
    (Finset.univ : Finset {c : Fin 50 // c ∈ (e i).val}).sort.map
      (fun c => (i, Shared50Dirty.partialRole (e i) c)))

def read (e : Fin n ≃ Triple 50) : Program (DirtyLinearCircuit.Register n 509194) (ZMod 2) :=
  SparseCircuit.copies DirtyLinearCircuit.y DirtyLinearCircuit.scratch (readEntries e)

@[simp] theorem load_length (e : Fin n ≃ Triple 50) : (load e).length = SharedPointExecution.code.sources.length := by
  simp [load, sourceEntries]

/-- Sparse loading never writes the same physical source destination twice. -/
theorem source_targets_nodup (e : Fin n ≃ Triple 50) : ((sourceEntries e).map Prod.fst).Nodup := by
  simpa only [sourceEntries, List.map_map, Function.comp_def] using source_roles_nodup

theorem load_length_bound (e : Fin n ≃ Triple 50) : (load e).length ≤ 509194 := by
  have hh := source_roles_nodup.length_le_card
  simpa only [List.length_map, List.length_attach, Fintype.card_fin, load_length] using hh

private theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_map_sort {α M : Type*} [LinearOrder α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) : (s.sort.map f).sum = ∑ x ∈ s, f x := by
  simpa using (List.sum_toFinset f (Finset.sort_nodup s (· ≤ ·))).symm

@[simp] theorem read_length (e : Fin n ≃ Triple 50) : (read e).length = 3 * n := by
  have hc (i : Fin n) : (e i).val.card = 3 := (e i).property
  simp [read, readEntries, List.length_flatMap, List.map_ofFn, List.sum_ofFn, hc, Nat.mul_comm]

/-- The source-copy payload is exactly the original compiler's source initialization. -/
theorem source_sum (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) (role : Fin 509194) :
    ((sourceEntries e).map (fun entry => if entry.1 = role then X entry.2 else 0)).sum =
      Shared50Finite.initial (fun T => X (e.symm T)) role := by
  change _ = DAGValueTransfer.initial SharedPointExecution.code.sources
    (DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T))) role.val
  rw [DAGSourceRoles.initial_as_sum]
  unfold sourceEntries
  rw [List.map_map]
  calc
    _ = (SharedPointExecution.code.sources.attach.map (fun entry =>
        if entry.val.2 = role.val then
          DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T)) entry.val.1 else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro entry _
      simp only [Function.comp_def, sourceRole, Fin.ext_iff, sourceLabel,
        DAGSourceRoles.sourceInput_label circuit.nodes outputRefs entry.val (source_mem_compile entry)]
    _ = _ := congrArg List.sum (List.attach_map_val (f := fun entry : ℕ × ℕ =>
      if entry.2 = role.val then DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T)) entry.1 else 0))

/-- The readout-copy payload sums precisely the three physical partial outputs. -/
theorem read_sum (e : Fin n ≃ Triple 50) (S : Fin 509194 → ZMod 2) (i : Fin n) :
    ((readEntries e).map (fun entry => if entry.1 = i then S entry.2 else 0)).sum =
      mv (Shared50Dirty.readoutMatrix e) S i := by
  rw [Shared50Dirty.readoutMatrix_mv]
  simp only [readEntries, sum_map_flatMap, List.map_map, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, sum_map_sort]
  simp

/-- Sparse loading adds the real source values and preserves all data banks. -/
theorem load_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2) (S : Fin 509194 → ZMod 2) :
    run (load e) (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X Y (S + Shared50Finite.initial (fun T => X (e.symm T))) := by
  have hh := bank_load_run (sourceEntries e) X Y S
  have he : (fun i => ((sourceEntries e).map (fun entry => if entry.1 = i then X entry.2 else 0)).sum) =
      Shared50Finite.initial (fun T => X (e.symm T)) := funext (source_sum e X)
  rw [he] at hh
  exact hh

/-- Sparse readout preserves arbitrary scratch while adding its actual partial outputs. -/
theorem read_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2) (S : Fin 509194 → ZMod 2) :
    run (read e) (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X (Y + mv (Shared50Dirty.readoutMatrix e) S) S := by
  have hh := bank_read_run (readEntries e) X Y S
  have he : (fun i => ((readEntries e).map (fun entry => if entry.1 = i then S entry.2 else 0)).sum) =
      mv (Shared50Dirty.readoutMatrix e) S := funext (read_sum e S)
  rw [he] at hh
  exact hh

/-- Exact sparse loading incidences: only a certified source role is written,
and its sole coefficient-one source is the matching semantic data input. -/
theorem load_incidence (e : Fin n ≃ Triple 50)
    (gate : Gate (DirtyLinearCircuit.Register n 509194) (ZMod 2)) :
    gate ∈ load e ↔ ∃ entry : Source,
      gate.target = DirtyLinearCircuit.scratch (sourceRole entry) ∧
      gate.terms = [(DirtyLinearCircuit.x (e.symm (sourceLabel entry)), 1)] := by
  rw [load, SparseCircuit.mem_copies]
  constructor
  · rintro ⟨p, hp, ht, hs⟩
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨entry, ht, hs⟩
  · rintro ⟨entry, ht, hs⟩
    exact ⟨(sourceRole entry, e.symm (sourceLabel entry)),
      List.mem_map.mpr ⟨entry, List.mem_attach _ _, rfl⟩, ht, hs⟩

/-- Exact readout incidences: each target's three partial output registers
are the sole sources of its three XOR updates. -/
theorem read_incidence (e : Fin n ≃ Triple 50)
    (gate : Gate (DirtyLinearCircuit.Register n 509194) (ZMod 2)) :
    gate ∈ read e ↔ ∃ i : Fin n, ∃ c : {c : Fin 50 // c ∈ (e i).val},
      gate.target = DirtyLinearCircuit.y i ∧
      gate.terms = [(DirtyLinearCircuit.scratch (Shared50Dirty.partialRole (e i) c), 1)] := by
  rw [read, SparseCircuit.mem_copies]
  constructor
  · rintro ⟨p, hp, ht, hs⟩
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hp
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hi
    exact ⟨i,c,ht,hs⟩
  · rintro ⟨i,c,ht,hs⟩
    refine ⟨(i, Shared50Dirty.partialRole (e i) c), ?_, ht, hs⟩
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_ofFn.mpr ⟨i,rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨c, (Finset.mem_sort _).mpr (Finset.mem_univ _), rfl⟩

/-- Registers outside the real source bank are never targeted by sparse loading. -/
theorem load_preserves_nonsource (e : Fin n ≃ Triple 50)
    (state : DirtyLinearCircuit.Register n 509194 → ZMod 2) (role : Fin 509194)
    (hrole : ∀ entry : Source, sourceRole entry ≠ role) :
    run (load e) state (DirtyLinearCircuit.scratch role) = state (DirtyLinearCircuit.scratch role) := by
  apply run_preserves
  intro gate hg
  obtain ⟨entry, ht, _⟩ := (load_incidence e gate).mp hg
  rw [ht]
  intro he
  exact hrole entry (Sum.inr.inj (Sum.inr.inj he))

private theorem contents_eta (state : DirtyLinearCircuit.Register n 509194 → ZMod 2) :
    DirtyLinearCircuit.contents (state ∘ DirtyLinearCircuit.x) (state ∘ DirtyLinearCircuit.y)
      (state ∘ DirtyLinearCircuit.scratch) = state := by
  funext role
  rcases role with i | i | i <;> rfl

/-- Sparse loading and the original dense input matrix block have identical
execution on every register state, including arbitrary scratch contents. -/
theorem load_eq_dense (e : Fin n ≃ Triple 50)
    (state : DirtyLinearCircuit.Register n 509194 → ZMod 2) :
    run (load e) state = run (block DirtyLinearCircuit.scratch DirtyLinearCircuit.x
      (Shared50Dirty.inputMatrix e)) state := by
  conv_lhs => rw [← contents_eta state]
  conv_rhs => rw [← contents_eta state]
  rw [load_run, DirtyLinearCircuit.inject_run, Shared50Dirty.inputMatrix_mv]

/-- Sparse readout equals the original dense matrix block on every register state. -/
theorem read_eq_dense (e : Fin n ≃ Triple 50)
    (state : DirtyLinearCircuit.Register n 509194 → ZMod 2) :
    run (read e) state = run (block DirtyLinearCircuit.y DirtyLinearCircuit.scratch
      (Shared50Dirty.readoutMatrix e)) state := by
  conv_lhs => rw [← contents_eta state]
  conv_rhs => rw [← contents_eta state]
  rw [read_run, DirtyLinearCircuit.read_run]

end Lists

end IntegerMultBounds.Networks.Shared50SparseIO
