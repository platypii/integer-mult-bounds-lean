import IntegerMultBounds.Networks.Shared50SparseIO
import IntegerMultBounds.Networks.Shared50SparseCentral
import IntegerMultBounds.Networks.Shared50Exchange

/-! The actual sparse twelve-block shared invocation and its local exchange.
All IO and central updates are one-source XORs. The certified finite DAG and
its literal reversal provide the four scratch-computation blocks. Scalar
execution and instruction counts below make no tape-time claim. -/

namespace IntegerMultBounds.Networks.Shared50SparseInvocation

open Circuit NeighborCounts

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50Finite.output Shared50Dirty.pairIndex Shared50Dirty.partialRole

private theorem role_load_run {n a c s : ℕ} (entries : List (Fin a × Fin n))
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2) (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies side x entries) (banks X Y A C S) =
      banks X Y (A + fun i => (entries.map (fun entry => if entry.1 = i then X entry.2 else 0)).sum) C S := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [side,x])]
  rcases role with i | i | i | i | i
  · simp [banks, side]
  · simp [banks, side]
  · simp [banks, side, x]
  · simp [banks, side]
  · simp [banks, side]

private theorem role_read_run {n a c s : ℕ} (entries : List (Fin n × Fin a))
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2) (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies y side entries) (banks X Y A C S) =
      banks X (Y + fun i => (entries.map (fun entry => if entry.1 = i then A entry.2 else 0)).sum) A C S := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [y,side])]
  rcases role with i | i | i | i | i
  · simp [banks, y]
  · simp [banks, y, side]
  · simp [banks, y]
  · simp [banks, y]
  · simp [banks, y]

variable {n s : ℕ}

/-- Only actual source slots receive one XOR from their associated data input. -/
def load (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  SparseCircuit.copies side x (Shared50SparseIO.sourceEntries e)

/-- Three actual partial-output source slots contribute to each target. -/
def read (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  SparseCircuit.copies y side (Shared50SparseIO.readEntries e)

/-- The actual finite shared DAG, embedded only into side scratch. -/
def forward (n s : ℕ) : Program (Role n 509194 50 s) (ZMod 2) :=
  GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) Shared50Finite.program

/-- Literal reversal of the scratch program, with the same physical embedding. -/
def backward (n s : ℕ) : Program (Role n 509194 50 s) (ZMod 2) :=
  GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) Shared50Finite.program.reverse

theorem load_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (load e) (banks X Y A C S) = banks X Y (A + mv (Shared50Dirty.inputMatrix e) X) C S := by
  have hh := role_load_run (Shared50SparseIO.sourceEntries e) X Y A C S
  have he := funext (Shared50SparseIO.source_sum e X)
  rw [he, ← Shared50Dirty.inputMatrix_mv] at hh
  exact hh

theorem read_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (read e) (banks X Y A C S) = banks X (Y + mv (Shared50Dirty.readoutMatrix e) A) A C S := by
  have hh := role_read_run (Shared50SparseIO.readEntries e) X Y A C S
  rw [funext (Shared50SparseIO.read_sum e A)] at hh
  exact hh

/-- Exactly the twelve sparse blocks in the optimized forward invocation. -/
def program (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  forward n s ++ (read e ++ (backward n s ++ (Shared50SparseCentral.scatter e ++
  (load e ++ (Shared50SparseCentral.gather e ++ (Shared50SparseCentral.scatter e ++
  (forward n s ++ (read e ++ (backward n s ++ (Shared50SparseCentral.gather e ++ load e))))))))))

/-- Sparse blocks have the exact execution of the proved twelve-block matrix
schedule. The equality concerns actual programs, not annotated costs. -/
theorem program_eq_dense (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (program e) (banks X Y A C S) = run (Shared50Invocation.program e) (banks X Y A C S) := by
  simp only [program, Shared50Invocation.program, Shared50Invocation.schedule, run_append,
    forward, backward, Shared50Invocation.side_run, read_run, load_run,
    Shared50SparseCentral.gather_run, Shared50SparseCentral.scatter_run,
    block_y_side, block_y_center, block_side_x, block_center_x]

/-- Actual sparse execution is the identity shear on the data banks and
restores arbitrary side/central scratch and spectators. -/
theorem program_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (program e) (banks X Y A C S) = banks X (Y + X) A C S := by
  rw [program_eq_dense, Shared50Invocation.program_run]

/-- Reverse block order and invert the scratch-computation blocks. Source-only
XOR blocks keep their internal order and remain self-inverse. -/
def inverse (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  load e ++ (Shared50SparseCentral.gather e ++ (forward n s ++ (read e ++
  (backward n s ++ (Shared50SparseCentral.scatter e ++ (Shared50SparseCentral.gather e ++
  (load e ++ (Shared50SparseCentral.scatter e ++ (forward n s ++ (read e ++ backward n s))))))))))

theorem inverse_eq_dense (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverse e) (banks X Y A C S) = run (Shared50Exchange.inverse e) (banks X Y A C S) := by
  simp only [inverse, Shared50Exchange.inverse, Shared50Exchange.inverseSchedule, run_append,
    forward, backward, Shared50Invocation.side_run, read_run, load_run,
    Shared50SparseCentral.gather_run, Shared50SparseCentral.scatter_run,
    block_y_side, block_y_center, block_side_x, block_center_x]

theorem inverse_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverse e) (banks X Y A C S) = banks X (Y + X) A C S := by
  rw [inverse_eq_dense, Shared50Exchange.inverse_run]

private theorem double {ι : Type*} (f : ι → ZMod 2) : f + f = 0 := by
  funext i
  simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using add_neg_cancel (f i)

theorem inverse_restores (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverse e) (run (program e) (banks X Y A C S)) = banks X Y A C S := by
  rw [program_run, inverse_run, add_assoc, double, add_zero]

private theorem renamed_run {n a c s : ℕ} (p : Program (Role n a c s) (ZMod 2))
    (hp : ∀ X Y A C S, run p (banks X Y A C S) = banks X (Y + X) A C S)
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2) (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (rename (exchangeRoles n a c s) p) (banks X Y A C S) = banks (X + Y) Y A C S := by
  have hh := run_rename (exchangeRoles n a c s) p (banks X Y A C S)
  rw [banks_exchange, hp] at hh
  funext k
  have hk := congrFun hh (exchangeRoles n a c s k)
  rcases k with i | i | i | i | i <;> exact hk

/-- Static register renaming for the opposite middle-stage orientation. -/
def opposite (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (inverse e)

theorem opposite_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (opposite e) (banks X Y A C S) = banks (X + Y) Y A C S :=
  renamed_run (inverse e) (inverse_run e) X Y A C S

/-- Three actual sparse invocation lists, sharing the same restored scratch. -/
def exchange (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  program e ++ (opposite e ++ program e)

theorem exchange_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (exchange e) (banks X Y A C S) = banks Y X A C S := by
  simp only [exchange, run_append, program_run, opposite_run]
  have hx : X + (Y + X) = Y := by
    have hh := double X
    linear_combination hh
  rw [hx, add_assoc Y X Y, add_comm X Y, ← add_assoc, double, zero_add]

@[simp] theorem load_length (e : Fin n ≃ Triple 50) :
    (load (s := s) e).length = SharedPointExecution.code.sources.length := by
  simp only [load, SparseCircuit.copies_length, Shared50SparseIO.sourceEntries,
    List.length_map, List.length_attach]

@[simp] theorem read_length (e : Fin n ≃ Triple 50) : (read (s := s) e).length = 3*n := by
  simpa only [read, Shared50SparseIO.read, SparseCircuit.copies_length] using Shared50SparseIO.read_length e

@[simp] theorem forward_length : (forward n s).length = Shared50Finite.program.length := by
  simp only [forward, GlobalCircuit.embed_length]

@[simp] theorem backward_length : (backward n s).length = Shared50Finite.program.length := by
  simp only [backward, GlobalCircuit.embed_length, List.length_reverse]

/-- Exact elementary instruction count of the actual sparse twelve-block list. -/
theorem program_length (e : Fin n ≃ Triple 50) :
    (program (s := s) e).length =
      4 * Shared50Finite.program.length + 2 * SharedPointExecution.code.sources.length + 18*n := by
  simp only [program, List.length_append, forward_length, backward_length, load_length, read_length,
    Shared50SparseCentral.gather_length, Shared50SparseCentral.scatter_length]
  omega

theorem inverse_length (e : Fin n ≃ Triple 50) :
    (inverse (s := s) e).length =
      4 * Shared50Finite.program.length + 2 * SharedPointExecution.code.sources.length + 18*n := by
  simp only [inverse, List.length_append, forward_length, backward_length, load_length, read_length,
    Shared50SparseCentral.gather_length, Shared50SparseCentral.scatter_length]
  omega

/-- Concrete scalar-instruction bound; this is not a bound on tape steps. -/
theorem instruction_bound (e : Fin n ≃ Triple 50) : (program (s := s) e).length ≤ 4856740 + 18*n := by
  rw [program_length]
  have hp := Shared50Finite.instruction_bound
  have hs := Shared50SparseIO.load_length_bound e
  rw [Shared50SparseIO.load_length] at hs
  omega

theorem instruction_bound50 (e : Fin 19600 ≃ Triple 50) :
    (program (s := s) e).length ≤ 5209540 := by
  simpa using instruction_bound (s := s) e

theorem exchange_length (e : Fin n ≃ Triple 50) :
    (exchange (s := s) e).length = 3 *
      (4 * Shared50Finite.program.length + 2 * SharedPointExecution.code.sources.length + 18*n) := by
  simp only [exchange, opposite, List.length_append, rename_length, program_length, inverse_length]
  omega

theorem exchange_instruction_bound50 (e : Fin 19600 ≃ Triple 50) :
    (exchange (s := s) e).length ≤ 15628620 := by
  have hp := instruction_bound50 (s := s) e
  rw [program_length] at hp
  rw [exchange_length]
  exact Nat.mul_le_mul_left 3 hp

end IntegerMultBounds.Networks.Shared50SparseInvocation
