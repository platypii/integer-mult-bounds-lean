import IntegerMultBounds.Networks.Scalar
import Mathlib.Data.List.FinRange

/-!
Executable scalar circuits for the cancellation schedule in Section 3.
Each instruction adds a finite linear combination of registers to one register.
This file counts these elementary instructions, not the manuscript's grouped
multi-output gates. It does not compile circuits to tape machines.
-/

namespace IntegerMultBounds.Networks.Circuit

/-- One elementary linear register update. Source values are read before writing. -/
structure Gate (ι R : Type*) where
  target : ι
  terms : List (ι × R)

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Evaluation is an ordinary finite sum and a single register write. -/
def Gate.run (g : Gate ι R) (r : ι → R) : ι → R :=
  Function.update r g.target (r g.target + (g.terms.map fun p => p.2 * r p.1).sum)

abbrev Program (ι R : Type*) := List (Gate ι R)

def run : Program ι R → (ι → R) → (ι → R)
  | [], r => r
  | g :: gs, r => run gs (g.run r)

@[simp] theorem run_nil (r : ι → R) : run [] r = r := rfl
@[simp] theorem run_cons (g : Gate ι R) (gs : Program ι R) (r : ι → R) :
    run (g :: gs) r = run gs (g.run r) := rfl

@[simp] theorem run_append (p q : Program ι R) (r : ι → R) :
    run (p ++ q) r = run q (run p r) := by
  induction p generalizing r with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- A register that is never a target is preserved, even if it is read. -/
theorem run_preserves (p : Program ι R) (r : ι → R) (k : ι)
    (h : ∀ g ∈ p, g.target ≠ k) : run p r k = r k := by
  induction p generalizing r with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (fun g hg => h g (by simp [hg]))]
    exact Function.update_of_ne (h g (by simp)).symm _ _

/-- One row of a matrix, with explicitly enumerated source registers. -/
def rowGate {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (i : Fin n) : Gate ι R :=
  ⟨dst i, List.ofFn fun j => (src j, M i j)⟩

@[simp] theorem rowGate_run {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (i : Fin n) (r : ι → R) :
    (rowGate dst src M i).run r =
      Function.update r (dst i) (r (dst i) + ∑ j, M i j * r (src j)) := by
  simp [Gate.run, rowGate, List.map_ofFn, List.sum_ofFn]

/-- Row-by-row executable matrix addition, with no runtime choice of registers. -/
def block {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) : Program ι R :=
  (List.ofFn (fun i : Fin n => i)).map (rowGate dst src M)

omit [DecidableEq ι] [CommRing R] in
@[simp] theorem block_length {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) : (block dst src M).length = n := by
  simp [block]

private theorem run_rows {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (separate : ∀ i j, dst i ≠ src j)
    (is : List (Fin n)) (r : ι → R) (k : ι) :
    run (is.map (rowGate dst src M)) r k =
      r k + (is.map fun i => if dst i = k then ∑ j, M i j * r (src j) else 0).sum := by
  induction is generalizing r with
  | nil => simp
  | cons i is ih =>
    rw [List.map_cons, run_cons, ih]
    have hs (j : Fin m) : (rowGate dst src M i).run r (src j) = r (src j) := by
      simp [rowGate_run, Function.update_of_ne (separate i j).symm]
    simp only [hs, List.map_cons, List.sum_cons]
    rw [rowGate_run]
    by_cases hk : dst i = k
    · subst k
      simp only [Function.update_self, ↓reduceIte]
      abel
    · simp [Function.update_of_ne (Ne.symm hk), hk]

/-- A disjoint source bank lets the sequential circuit implement simultaneous
matrix addition exactly; every register outside the target bank is preserved. -/
theorem block_run {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (separate : ∀ i j, dst i ≠ src j)
    (r : ι → R) (k : ι) :
    run (block dst src M) r k =
      r k + ∑ i, if dst i = k then ∑ j, M i j * r (src j) else 0 := by
  simpa [block, List.map_ofFn, List.sum_ofFn] using
    run_rows dst src M separate (List.ofFn (fun i : Fin n => i)) r k

theorem block_run_target {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (separate : ∀ i j, dst i ≠ src j)
    (injective : Function.Injective dst) (r : ι → R) (i : Fin n) :
    run (block dst src M) r (dst i) = r (dst i) + ∑ j, M i j * r (src j) := by
  rw [block_run dst src M separate]
  simp [injective.eq_iff]

theorem block_run_other {n m : ℕ} (dst : Fin n → ι) (src : Fin m → ι)
    (M : Fin n → Fin m → R) (r : ι → R) (k : ι)
    (outside : ∀ i, dst i ≠ k) : run (block dst src M) r k = r k := by
  apply run_preserves
  simp only [block, List.mem_map]
  rintro g ⟨i, _, rfl⟩
  exact outside i

/-- Two data banks, side scratch, central scratch, and arbitrary spectators. -/
abbrev Role (n a c s : ℕ) := Fin n ⊕ Fin n ⊕ Fin a ⊕ Fin c ⊕ Fin s

def x {n a c s : ℕ} (i : Fin n) : Role n a c s := Sum.inl i
def y {n a c s : ℕ} (i : Fin n) : Role n a c s := Sum.inr (Sum.inl i)
def side {n a c s : ℕ} (i : Fin a) : Role n a c s := Sum.inr (Sum.inr (Sum.inl i))
def center {n a c s : ℕ} (i : Fin c) : Role n a c s :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
def spectator {n a c s : ℕ} (i : Fin s) : Role n a c s :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))

/-- Register content assembled from its five finite banks. -/
def banks {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) : Role n a c s → R :=
  Sum.elim X (Sum.elim Y (Sum.elim A (Sum.elim C S)))

omit [CommRing R] in
@[simp] theorem banks_x {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) (i) : banks X Y A C S (x i) = X i := rfl
omit [CommRing R] in
@[simp] theorem banks_y {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) (i) : banks X Y A C S (y i) = Y i := rfl
omit [CommRing R] in
@[simp] theorem banks_side {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) (i) : banks X Y A C S (side i) = A i := rfl
omit [CommRing R] in
@[simp] theorem banks_center {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) (i) : banks X Y A C S (center i) = C i := rfl
omit [CommRing R] in
@[simp] theorem banks_spectator {n a c s : ℕ} (X Y : Fin n → R) (A : Fin a → R)
    (C : Fin c → R) (S : Fin s → R) (i) : banks X Y A C S (spectator i) = S i := rfl


/-- Matrix-vector application over the finite source bank. -/
def mv {n m : ℕ} (M : Fin n → Fin m → R) (v : Fin m → R) : Fin n → R :=
  fun i => ∑ j, M i j * v j

@[simp] theorem mv_add {n m : ℕ} (M : Fin n → Fin m → R) (v w : Fin m → R) :
    mv M (v + w) = mv M v + mv M w := by
  ext i
  simp [mv, mul_add, Finset.sum_add_distrib]

@[simp] theorem mv_neg {n m : ℕ} (M : Fin n → Fin m → R) (v : Fin m → R) :
    mv M (-v) = -mv M v := by
  ext i
  simp [mv, Finset.sum_neg_distrib]

@[simp] theorem mv_neg_matrix {n m : ℕ} (M : Fin n → Fin m → R) (v : Fin m → R) :
    mv (-M) v = -mv M v := by
  ext i
  simp [mv, Finset.sum_neg_distrib]

@[simp] theorem block_y_side {n a c s : ℕ} (J : Fin n → Fin a → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (block y side J) (banks X Y A C S) = banks X (Y + mv J A) A C S := by
  funext k
  rw [block_run _ _ _ (by intros; simp [y, side])]
  rcases k with i | i | i | i | i <;> simp [y, side, banks, mv]

@[simp] theorem block_y_center {n a c s : ℕ} (H : Fin n → Fin c → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (block y center H) (banks X Y A C S) = banks X (Y + mv H C) A C S := by
  funext k
  rw [block_run _ _ _ (by intros; simp [y, center])]
  rcases k with i | i | i | i | i <;> simp [y, center, banks, mv]

@[simp] theorem block_side_x {n a c s : ℕ} (V : Fin a → Fin n → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (block side x V) (banks X Y A C S) = banks X Y (A + mv V X) C S := by
  funext k
  rw [block_run _ _ _ (by intros; simp [side, x])]
  rcases k with i | i | i | i | i <;> simp [x, side, banks, mv]

@[simp] theorem block_center_x {n a c s : ℕ} (G : Fin c → Fin n → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (block center x G) (banks X Y A C S) = banks X Y A (C + mv G X) S := by
  funext k
  rw [block_run _ _ _ (by intros; simp [center, x])]
  rcases k with i | i | i | i | i <;> simp [x, center, banks, mv]

/-- The eight rows, expanded into finite elementary instructions. -/
def dirty {n a c s : ℕ} (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) : Program (Role n a c s) R :=
  block y side (-J) ++ block y center (-H) ++ block side x V ++ block center x G ++
  block y center H ++ block y side J ++ block center x (-G) ++ block side x (-V)

/-- Concrete elementary gate count, rather than an abstract cost annotation. -/
@[simp] theorem dirty_length {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (dirty (s := s) V G J H).length = 4 * n + 2 * a + 2 * c := by
  simp [dirty]
  omega

/-- Unconditional correctness of the executable cancellation schedule. Both
scratch banks and all spectators are restored for arbitrary initial values. -/
theorem dirty_run {n a c s : ℕ} (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (dirty V G J H) (banks X Y A C S) =
      banks X (Y + (mv J (mv V X) + mv H (mv G X))) A C S := by
  simp only [dirty, run_append, block_y_side, block_y_center, block_side_x,
    block_center_x, mv_neg_matrix, mv_add]
  congr 1 <;> ext i <;> simp only [Pi.add_apply, Pi.neg_apply] <;> abel

/-- When the concrete matrices reconstruct the source bank, the compiled
schedule is a shear on the data banks and the identity on all other registers. -/
theorem dirty_run_shear {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (reconstruct : ∀ X, mv J (mv V X) + mv H (mv G X) = X)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (dirty V G J H) (banks X Y A C S) = banks X (Y + X) A C S := by
  rw [dirty_run, reconstruct]

/-- The inverse rows in their required reversed order. This is the stage-two
schedule before exchanging the logical source and target bank names. -/
def dirtyInverse {n a c s : ℕ} (V : Fin a → Fin n → R) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) : Program (Role n a c s) R :=
  block side x V ++ block center x G ++ block y side (-J) ++ block y center (-H) ++
  block center x (-G) ++ block side x (-V) ++ block y center H ++ block y side J

@[simp] theorem dirtyInverse_length {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (dirtyInverse (s := s) V G J H).length = 4 * n + 2 * a + 2 * c := by
  simp [dirtyInverse]
  omega

/-- The reversed schedule subtracts the reconstructed source bank, with no
clean-scratch precondition. -/
theorem dirtyInverse_run {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    run (dirtyInverse V G J H) (banks X Y A C S) =
      banks X (Y - (mv J (mv V X) + mv H (mv G X))) A C S := by
  simp only [dirtyInverse, run_append, block_y_side, block_y_center, block_side_x,
    block_center_x, mv_neg_matrix, mv_add, mv_neg]
  congr 1 <;> ext i <;> simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] <;> abel

/-- Direct verification of inverse behavior for every possible register state. -/
theorem dirtyInverse_run_dirty {n a c s : ℕ} (V : Fin a → Fin n → R)
    (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (r : Role n a c s → R) : run (dirtyInverse V G J H) (run (dirty V G J H) r) = r := by
  have hr : r = banks (r ∘ x) (r ∘ y) (r ∘ side) (r ∘ center) (r ∘ spectator) := by
    funext k
    rcases k with i | i | i | i | i <;> rfl
  conv_lhs => rw [hr]
  rw [dirty_run, dirtyInverse_run, add_sub_cancel_right]
  exact hr.symm

end IntegerMultBounds.Networks.Circuit


