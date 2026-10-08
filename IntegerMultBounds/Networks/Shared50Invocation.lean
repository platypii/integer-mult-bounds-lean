import IntegerMultBounds.Networks.Shared50Dirty
import IntegerMultBounds.Networks.CircuitBits

/-! The literal twelve-block optimized invocation. The actual shared DAG
implements the side map; the fifty central sums complete the identity. Every
side and central scratch value is restored. Frame and tape costs are separate. -/

namespace IntegerMultBounds.Networks.Shared50Invocation

open Circuit NeighborCounts

variable {n a c s : ℕ}

def sideEmbedding (n a c s : ℕ) : Fin a ↪ Role n a c s :=
  ⟨side, fun _ _ he => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj he))⟩

theorem side_run (p : Program (Fin a) (ZMod 2)) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (GlobalCircuit.embed (sideEmbedding n a c s) p) (banks X Y A C S) =
      banks X Y (run p A) C S := by
  have he := GlobalCircuit.embed_run (sideEmbedding n a c s) p (banks X Y A C S)
  funext r
  rcases r with i | i | i | i | i
  · exact GlobalCircuit.embed_outside _ _ _ (x i) (by intro j; change side j ≠ x i; simp [side, x])
  · exact GlobalCircuit.embed_outside _ _ _ (y i) (by intro j; change side j ≠ y i; simp [side, y])
  · exact congrFun he i
  · exact GlobalCircuit.embed_outside _ _ _ (center i) (by intro j; change side j ≠ center i; simp [side, center])
  · exact GlobalCircuit.embed_outside _ _ _ (spectator i) (by intro j; change side j ≠ spectator i; simp [side, spectator])

/-- Exactly L, J, L inverse, R, V, G, R, L, J, L inverse, G, V. -/
def schedule (L Li : Program (Fin a) (ZMod 2))
    (V : Fin a → Fin n → ZMod 2) (J : Fin n → Fin a → ZMod 2)
    (G : Fin c → Fin n → ZMod 2) (R : Fin n → Fin c → ZMod 2) :
    Program (Role n a c s) (ZMod 2) :=
  GlobalCircuit.embed (sideEmbedding n a c s) L ++ block y side J ++
  GlobalCircuit.embed (sideEmbedding n a c s) Li ++ block y center R ++
  block side x V ++ block center x G ++ block y center R ++
  GlobalCircuit.embed (sideEmbedding n a c s) L ++ block y side J ++
  GlobalCircuit.embed (sideEmbedding n a c s) Li ++ block center x G ++ block side x V

private theorem double (f : Fin a → ZMod 2) : f + f = 0 := by
  funext i
  simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using add_neg_cancel (f i)

/-- Literal schedule execution, with arbitrary dirty side/central scratch. -/
theorem schedule_run (L Li : Program (Fin a) (ZMod 2))
    (V : Fin a → Fin n → ZMod 2) (J : Fin n → Fin a → ZMod 2)
    (G : Fin c → Fin n → ZMod 2) (R : Fin n → Fin c → ZMod 2)
    (hinv : ∀ A, run Li (run L A) = A)
    (X Y : Fin n → ZMod 2) (A : Fin a → ZMod 2)
    (C : Fin c → ZMod 2) (S : Fin s → ZMod 2) :
    run (schedule L Li V J G R) (banks X Y A C S) =
      banks X (Y + (mv J (run L (mv V X)) + mv R (mv G X))) A C S := by
  simp only [schedule, run_append, side_run, block_y_side, block_y_center,
    block_side_x, block_center_x, hinv, DirtyLinearCircuit.run_add, mv_add]
  have ha : A + mv V X + mv V X = A := by rw [add_assoc, double, add_zero]
  have hc : C + mv G X + mv G X = C := by rw [add_assoc, double, add_zero]
  rw [ha, hc]
  congr 1
  have hJ := double (mv J (run L A))
  have hR := double (mv R C)
  linear_combination hJ + hR

/-- The neighbor side map and the fifty coordinate sums reconstruct the input. -/
theorem reconstruct (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) :
    Shared50Dirty.neighborMap e X +
      mv (bitScatter (fun i => (e i).val)) (mv (bitGather (fun i => (e i).val)) X) = X := by
  have hside : Shared50Dirty.neighborMap e X =
      mv (fun i j => if BitNeighbor (e j) (e i) then 1 else 0) X := by
    funext i
    rw [Shared50Dirty.neighborMap, mv, ← e.sum_comp]
    simp
  rw [hside]
  funext i
  simp only [Pi.add_apply, mv]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  have coeff (j : Fin n) :
      (if BitNeighbor (e j) (e i) then (1 : ZMod 2) else 0) +
        (∑ k, bitScatter (fun i => (e i).val) i k * bitGather (fun i => (e i).val) k j) =
      if i = j then 1 else 0 := by
    rw [bit_central_coeff]
    have h := bitCoefficient_eq (e i).val (e j).val (e i).property (e j).property
    have hinj : (e i).val = (e j).val ↔ i = j := by
      rw [← Subtype.ext_iff, e.injective.eq_iff]
    have hb : BitNeighbor (e j) (e i) ↔ ((e i).val ∩ (e j).val).card = 1 := by
      simp only [BitNeighbor, Finset.inter_comm]
    simp only [hb]
    have hc := congrArg (fun v : ℕ => (v : ZMod 2)) h
    simp only [bitCoefficient, ZMod.natCast_mod, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, hinj] at hc
    simpa only [add_comm] using hc
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← add_mul, coeff]
  simp

/-- The actual optimized invocation, with the original fifty central registers. -/
def program (e : Fin n ≃ Triple 50) : Program (Role n 509194 50 s) (ZMod 2) :=
  schedule Shared50Finite.program Shared50Finite.program.reverse
    (Shared50Dirty.inputMatrix e) (Shared50Dirty.readoutMatrix e)
    (bitGather (fun i => (e i).val)) (bitScatter (fun i => (e i).val))

theorem program_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2)
    (A : Fin 509194 → ZMod 2) (C : Fin 50 → ZMod 2) (S : Fin s → ZMod 2) :
    run (program e) (banks X Y A C S) = banks X (Y + X) A C S := by
  rw [program, schedule_run _ _ _ _ _ _ Shared50Finite.reverse_run,
    Shared50Dirty.readout_execution, reconstruct]

end IntegerMultBounds.Networks.Shared50Invocation
