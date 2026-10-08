import IntegerMultBounds.Networks.Shared50Invocation
import IntegerMultBounds.Networks.SparseCircuit
import Mathlib.Data.Finset.Sort

/-! Sparse central gather/scatter for the optimized invocation. Each emitted
instruction has one source and coefficient one; each triple contributes exactly
three instructions, and execution equals the existing central matrices. -/

namespace IntegerMultBounds.Networks.Shared50SparseCentral

open Circuit NeighborCounts

variable {n a s : ℕ}

/-- Concrete input-coordinate incidences, ordered by input index and coordinate. -/
def entries (e : Fin n ≃ Triple 50) : List (Fin n × Fin 50) :=
  (List.ofFn (fun i : Fin n => i)).flatMap (fun i =>
    ((e i).val.sort (· ≤ ·)).map (fun c => (i,c)))

private theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_sort {α M : Type*} [LinearOrder α] [AddCommMonoid M]
    (t : Finset α) (f : α → M) : ((t.sort (· ≤ ·)).map f).sum = ∑ c ∈ t, f c := by
  simpa using (List.sum_toFinset f (t.sort_nodup (· ≤ ·))).symm

theorem entries_length (e : Fin n ≃ Triple 50) : (entries e).length = 3 * n := by
  simp [entries, List.length_flatMap, List.map_ofFn, List.sum_ofFn, (e _).property, Nat.mul_comm]

theorem mem_entries (e : Fin n ≃ Triple 50) (i : Fin n) (c : Fin 50) :
    (i,c) ∈ entries e ↔ c ∈ (e i).val := by
  simp [entries]

/-- Three central XORs per input triple. -/
def gather (e : Fin n ≃ Triple 50) : Program (Role n a 50 s) (ZMod 2) :=
  SparseCircuit.copies center x ((entries e).map Prod.swap)

/-- Three central XORs per output triple. -/
def scatter (e : Fin n ≃ Triple 50) : Program (Role n a 50 s) (ZMod 2) :=
  SparseCircuit.copies y center (entries e)

@[simp] theorem gather_length (e : Fin n ≃ Triple 50) : (gather (a := a) (s := s) e).length = 3*n := by
  simp [gather, entries_length]

@[simp] theorem scatter_length (e : Fin n ≃ Triple 50) : (scatter (a := a) (s := s) e).length = 3*n := by
  simp [scatter, entries_length]

theorem gather_sum (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) (c : Fin 50) :
    ((entries e).map (fun entry => if entry.2 = c then X entry.1 else 0)).sum =
      mv (bitGather (fun i => (e i).val)) X c := by
  simp only [entries, sum_map_flatMap, List.map_map, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, sum_sort]
  simp [mv, bitGather, Finset.sum_ite_eq', ite_mul]

theorem scatter_sum (e : Fin n ≃ Triple 50) (C : Fin 50 → ZMod 2) (i : Fin n) :
    ((entries e).map (fun entry => if entry.1 = i then C entry.2 else 0)).sum =
      mv (bitScatter (fun i => (e i).val)) C i := by
  simp only [entries, sum_map_flatMap, List.map_map, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, sum_sort]
  simp [mv, bitScatter, Finset.sum_ite_irrel, ite_mul]

theorem gather_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (gather e) (banks X Y A C S) =
      banks X Y A (C + mv (bitGather (fun i => (e i).val)) X) S := by
  funext r
  rw [gather, SparseCircuit.copies_run _ _ _ (by intros; simp [center,x])]
  simp only [List.map_map, Function.comp_def, Prod.swap]
  rcases r with i | i | i | i | i
  · simp [banks, center]
  · simp [banks, center]
  · simp [banks, center]
  · simpa only [banks, center, x, Sum.inr.injEq, Sum.inl.injEq, Sum.elim_inl, Sum.elim_inr, Pi.add_apply] using
      congrArg (C i + ·) (gather_sum e X i)
  · simp [banks, center]

theorem scatter_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (scatter e) (banks X Y A C S) =
      banks X (Y + mv (bitScatter (fun i => (e i).val)) C) A C S := by
  funext r
  rw [scatter, SparseCircuit.copies_run _ _ _ (by intros; simp [y,center])]
  rcases r with i | i | i | i | i
  · simp [banks, y]
  · simpa only [banks, y, center, Sum.inr.injEq, Sum.inl.injEq, Sum.elim_inl, Sum.elim_inr, Pi.add_apply] using
      congrArg (Y i + ·) (scatter_sum e C i)
  · simp [banks, y]
  · simp [banks, y]
  · simp [banks, y]

/-- Actual central gather incidences are exactly triple membership incidences. -/
theorem gather_incidence (e : Fin n ≃ Triple 50) (gate : Gate (Role n a 50 s) (ZMod 2)) :
    gate ∈ gather e ↔ ∃ i c, c ∈ (e i).val ∧
      gate.target = center c ∧ gate.terms = [(x i,1)] := by
  rw [gather, SparseCircuit.mem_copies]
  constructor
  · rintro ⟨entry, he, ht, hs⟩
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp he
    exact ⟨pair.1, pair.2, (mem_entries e _ _).mp hp, ht, hs⟩
  · rintro ⟨i,c,hc,ht,hs⟩
    exact ⟨(c,i), List.mem_map.mpr ⟨(i,c), (mem_entries e _ _).mpr hc, rfl⟩, ht, hs⟩

theorem scatter_incidence (e : Fin n ≃ Triple 50) (gate : Gate (Role n a 50 s) (ZMod 2)) :
    gate ∈ scatter e ↔ ∃ i c, c ∈ (e i).val ∧
      gate.target = y i ∧ gate.terms = [(center c,1)] := by
  rw [scatter, SparseCircuit.mem_copies]
  constructor
  · rintro ⟨⟨i,c⟩, he, ht, hs⟩
    exact ⟨i,c,(mem_entries e _ _).mp he,ht,hs⟩
  · rintro ⟨i,c,hc,ht,hs⟩
    exact ⟨(i,c),(mem_entries e _ _).mpr hc,ht,hs⟩

end IntegerMultBounds.Networks.Shared50SparseCentral
