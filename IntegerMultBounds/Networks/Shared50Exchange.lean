import IntegerMultBounds.Networks.Shared50Invocation

/-! The optimized local invocation, explicitly inverted and oriented in the
opposite direction for the middle stage. These are actual instruction lists
with arbitrary dirty scratch; global placement and frame ranks are separate. -/

namespace IntegerMultBounds.Networks.Shared50Exchange

open Circuit NeighborCounts Shared50Invocation

attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit

variable {n a c s : ℕ}

/-- Invert the twelve blocks in reverse order. Each matrix block is its own
inverse in characteristic two, and scratch computations exchange L and Li.
The row order inside a matrix block is retained. -/
def inverseSchedule (L Li : Program (Fin a) (ZMod 2))
    (V : Fin a → Fin n → ZMod 2) (J : Fin n → Fin a → ZMod 2)
    (G : Fin c → Fin n → ZMod 2) (R : Fin n → Fin c → ZMod 2) :
    Program (Role n a c s) (ZMod 2) :=
  block side x V ++ block center x G ++
  GlobalCircuit.embed (sideEmbedding n a c s) L ++ block y side J ++
  GlobalCircuit.embed (sideEmbedding n a c s) Li ++ block y center R ++
  block center x G ++ block side x V ++ block y center R ++
  GlobalCircuit.embed (sideEmbedding n a c s) L ++ block y side J ++
  GlobalCircuit.embed (sideEmbedding n a c s) Li

private theorem double (f : Fin a → ZMod 2) : f + f = 0 := by
  funext i
  simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using add_neg_cancel (f i)

theorem inverseSchedule_run (L Li : Program (Fin a) (ZMod 2))
    (V : Fin a → Fin n → ZMod 2) (J : Fin n → Fin a → ZMod 2)
    (G : Fin c → Fin n → ZMod 2) (R : Fin n → Fin c → ZMod 2)
    (hinv : ∀ A, run Li (run L A) = A)
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2)
    (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverseSchedule L Li V J G R) (banks X Y A C S) =
      banks X (Y + (mv J (run L (mv V X)) + mv R (mv G X))) A C S := by
  simp only [inverseSchedule, run_append, side_run, block_y_side, block_y_center,
    block_side_x, block_center_x, hinv]
  have ha : A + mv V X + mv V X = A := by rw [add_assoc, double, add_zero]
  have hc : C + mv G X + mv G X = C := by rw [add_assoc, double, add_zero]
  rw [ha, hc]
  simp only [DirtyLinearCircuit.run_add, mv_add]
  congr 1
  have hJ := double (mv J (run L A))
  have hR := double (mv R C)
  linear_combination hJ + hR

/-- The actual reversed block schedule specialized to the certified shared DAG. -/
def inverse (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  inverseSchedule Shared50Finite.program Shared50Finite.program.reverse
    (Shared50Dirty.inputMatrix e) (Shared50Dirty.readoutMatrix e)
    (bitGather (fun i => (e i).val)) (bitScatter (fun i => (e i).val))

theorem inverse_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverse e) (banks X Y A C S) = banks X (Y + X) A C S := by
  rw [inverse, inverseSchedule_run _ _ _ _ _ _ Shared50Finite.reverse_run,
    Shared50Dirty.readout_execution, reconstruct]

/-- The explicit reversed block schedule really inverts the actual invocation. -/
theorem inverse_restores (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (inverse e) (run (Shared50Invocation.program e) (banks X Y A C S)) = banks X Y A C S := by
  rw [Shared50Invocation.program_run, inverse_run, add_assoc, double, add_zero]

/-- Opposite orientation is a static register renaming of the inverse list. -/
def opposite (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (inverse e)

private theorem renamed_run (p : Program (Role n a c s) (ZMod 2))
    (hp : ∀ X Y A C S, run p (banks X Y A C S) = banks X (Y + X) A C S)
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2) (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (rename (exchangeRoles n a c s) p) (banks X Y A C S) = banks (X + Y) Y A C S := by
  have hh := run_rename (exchangeRoles n a c s) p (banks X Y A C S)
  rw [banks_exchange, hp] at hh
  funext k
  have hk := congrFun hh (exchangeRoles n a c s k)
  rcases k with i | i | i | i | i <;> exact hk

theorem opposite_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (opposite e) (banks X Y A C S) = banks (X + Y) Y A C S :=
  renamed_run (inverse e) (inverse_run e) X Y A C S

/-- Three actual local invocation lists using the same dirty scratch banks. -/
def program (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  Shared50Invocation.program e ++ opposite e ++ Shared50Invocation.program e

/-- Full local exchange restores all original side/central scratch and spectators. -/
theorem program_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (program e) (banks X Y A C S) = banks Y X A C S := by
  simp only [program, run_append, Shared50Invocation.program_run, opposite_run]
  have hx : X + (Y + X) = Y := by
    have hh := double X
    linear_combination hh
  rw [hx, add_assoc Y X Y, add_comm X Y, ← add_assoc, double, zero_add]

end IntegerMultBounds.Networks.Shared50Exchange
