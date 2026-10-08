import IntegerMultBounds.Networks.BinaryWalsh
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Actual array operators on several binary address columns. Each local
translation kernel acts on one column slice; commuting those concrete operators
regroups an edge into one all-column factor per residual direction. -/

namespace IntegerMultBounds.Networks.BinaryColumns

open Module BinaryPhase BinaryWalsh

abbrev Address (h k : ℕ) := Fin k → BinaryWalsh.Address h
abbrev Arrays (h k : ℕ) := Address h k → ℂ
abbrev Operator (h k : ℕ) := Arrays h k →ₗ[ℂ] Arrays h k

/-- Apply a one-column operator to every slice with all other columns fixed. -/
noncomputable def liftColumn {h k : ℕ} (j : Fin k)
    (T : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) : Operator h k where
  toFun f x := T (fun y => f (Function.update x j y)) (x j)
  map_add' f g := by
    ext x
    change T ((fun y => f (Function.update x j y)) + (fun y => g (Function.update x j y))) (x j) = _
    rw [map_add]
    rfl
  map_smul' t f := by
    ext x
    change T (t • (fun y => f (Function.update x j y))) (x j) = _
    rw [map_smul]
    rfl

@[simp] theorem liftColumn_one {h k : ℕ} (j : Fin k) : liftColumn (h := h) j 1 = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  simp [liftColumn, Function.update_eq_self]

theorem liftColumn_mul {h k : ℕ} (j : Fin k)
    (T S : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) :
    liftColumn j (T * S) = liftColumn j T * liftColumn j S := by
  apply LinearMap.ext
  intro f
  funext x
  change T (S (fun y => f (Function.update x j y))) (x j) =
    T (fun y => S (fun z => f (Function.update (Function.update x j y) j z))
      ((Function.update x j y) j)) (x j)
  simp only [Function.update_self, Function.update_idem]

/-- A column slice has the ordinary finite matrix expansion. -/
theorem liftColumn_apply_sum {h k : ℕ} (j : Fin k)
    (T : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) (f : Arrays h k) (x : Address h k) :
    liftColumn j T f x = ∑ y, f (Function.update x j y) *
      T (fun z => if y = z then 1 else 0) (x j) := by
  change T (fun y => f (Function.update x j y)) (x j) = _
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Arbitrary linear operators on distinct column slices commute. -/
theorem liftColumn_commute {h k : ℕ} (i j : Fin k) (hij : i ≠ j)
    (T S : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) :
    Commute (liftColumn i T) (liftColumn j S) := by
  apply LinearMap.ext
  intro f
  funext x
  change liftColumn i T (liftColumn j S f) x = liftColumn j S (liftColumn i T f) x
  simp only [liftColumn_apply_sum, Function.update_of_ne hij,
    Function.update_of_ne (Ne.symm hij), Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Function.update_comm hij]
  ring

/-- Shift exactly one column, preserving every other component of the address. -/
def shift {h k : ℕ} (j : Fin k) (v : BinaryWalsh.Address h) (x : Address h k) : Address h k :=
  Function.update x j (x j + v)

/-- Column shifts commute both for distinct columns and for a shared column. -/
theorem shift_commute {h k : ℕ} (i j : Fin k) (v w : BinaryWalsh.Address h) (x : Address h k) :
    shift i v (shift j w x) = shift j w (shift i v x) := by
  by_cases hij : i = j
  · subst j
    funext l
    by_cases hl : l = i
    · subst l
      simp [shift, add_comm, add_left_comm]
    · simp [shift, Function.update_of_ne hl]
  · funext l
    by_cases hi : l = i
    · subst l
      simp [shift, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    · by_cases hj : l = j
      · subst l
        simp [shift, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
      · simp [shift, Function.update_of_ne hi, Function.update_of_ne hj]

noncomputable def columnTranslation {h k : ℕ} (j : Fin k) (v : BinaryWalsh.Address h) : Operator h k where
  toFun f x := f (shift j v x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal two-term translation kernel acting on a single column. -/
noncomputable def columnKernel {h k : ℕ} (j : Fin k) (q : ZMod 4)
    (v : BinaryWalsh.Address h) : Operator h k :=
  ((1 + phase q) / 2) • LinearMap.id + ((1 - phase q) / 2) • columnTranslation j v

@[simp] theorem columnKernel_apply {h k : ℕ} (j : Fin k) (q : ZMod 4)
    (v : BinaryWalsh.Address h) (f : Arrays h k) (x : Address h k) :
    columnKernel j q v f x = ((1 + phase q) / 2) * f x +
      ((1 - phase q) / 2) * f (shift j v x) := rfl

theorem liftColumn_kernel {h k : ℕ} (j : Fin k) (q : ZMod 4) (v : BinaryWalsh.Address h) :
    liftColumn j (kernel q v) = columnKernel j q v := by
  apply LinearMap.ext
  intro f
  funext x
  simp [liftColumn, kernel_apply, shift, Function.update_eq_self]

/-- Commutation is proved for concrete array functions, not merely tensor labels. -/
theorem columnKernel_commute {h k : ℕ} (i j : Fin k) (q r : ZMod 4)
    (v w : BinaryWalsh.Address h) : Commute (columnKernel i q v) (columnKernel j r w) := by
  change columnKernel i q v * columnKernel j r w = columnKernel j r w * columnKernel i q v
  apply LinearMap.ext
  intro f
  funext x
  change columnKernel i q v (columnKernel j r w f) x = columnKernel j r w (columnKernel i q v f) x
  simp only [columnKernel_apply]
  rw [shift_commute i j v w x]
  ring

/-- Multiplication distributes through a list when the cross terms commute. -/
private theorem prod_map_mul_commute {ι M : Type*} [Monoid M] (xs : List ι)
    (f g : ι → M) (hc : ∀ i j, Commute (f i) (g j)) :
    (xs.map (fun i => f i * g i)).prod = (xs.map f).prod * (xs.map g).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh : Commute (g x) (xs.map f).prod :=
      Commute.list_prod_right _ _ (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
        exact (hc i x).symm)
    simp only [List.map_cons, List.prod_cons, ih]
    calc
      f x * g x * ((xs.map f).prod * (xs.map g).prod) =
          f x * (g x * (xs.map f).prod) * (xs.map g).prod := by simp only [mul_assoc]
      _ = f x * ((xs.map f).prod * g x) * (xs.map g).prod := by rw [hh.eq]
      _ = f x * (xs.map f).prod * (g x * (xs.map g).prod) := by simp only [mul_assoc]

private theorem prod_map_mul_nodup {ι M : Type*} [Monoid M] (xs : List ι)
    (hn : xs.Nodup) (f g : ι → M) (hc : ∀ i j, i ≠ j → Commute (f i) (g j)) :
    (xs.map (fun i => f i * g i)).prod = (xs.map f).prod * (xs.map g).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hn⟩ := List.nodup_cons.mp hn
    have hh : Commute (g x) (xs.map f).prod :=
      Commute.list_prod_right _ _ (by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
        exact (hc i x (by intro he; subst i; exact hx hi)).symm)
    simp only [List.map_cons, List.prod_cons, ih hn]
    calc
      f x * g x * ((xs.map f).prod * (xs.map g).prod) =
          f x * (g x * (xs.map f).prod) * (xs.map g).prod := by simp only [mul_assoc]
      _ = f x * ((xs.map f).prod * g x) * (xs.map g).prod := by rw [hh.eq]
      _ = f x * (xs.map f).prod * (g x * (xs.map g).prod) := by simp only [mul_assoc]

/-- Transpose a finite rectangle of pairwise commuting operators. -/
private theorem prod_rectangle {ι κ M : Type*} [Monoid M] (xs : List ι) (ys : List κ)
    (F : ι → κ → M) (hc : ∀ i j i' j', Commute (F i j) (F i' j')) :
    (xs.map (fun i => (ys.map (F i)).prod)).prod =
      (ys.map (fun j => (xs.map (fun i => F i j)).prod)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    symm
    apply prod_map_mul_commute
    intro j j'
    apply Commute.list_prod_right
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact hc x j i j'

theorem liftColumn_prod {h k : ℕ} (j : Fin k)
    (ts : List (BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h)) :
    liftColumn j ts.prod = (ts.map (liftColumn j)).prod := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.prod_cons, liftColumn_mul, ih, List.map_cons]

/-- Apply the same operator to all `k` genuine column slices. -/
noncomputable def tensorColumns {h : ℕ} (k : ℕ)
    (T : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) : Operator h k :=
  (List.ofFn (fun j : Fin k => liftColumn j T)).prod

/-- Applying a composed operator in every column is composition of the two
whole-array operators; distinct-column commutation supplies the regrouping. -/
theorem tensorColumns_mul {h k : ℕ}
    (T S : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) :
    tensorColumns k (T * S) = tensorColumns k T * tensorColumns k S := by
  unfold tensorColumns
  simp only [liftColumn_mul]
  have hh := prod_map_mul_nodup (List.ofFn (fun j : Fin k => j))
    (List.nodup_ofFn.mpr (fun _ _ hh => hh))
    (fun j => liftColumn j T) (fun j => liftColumn j S)
    (fun i j hij => liftColumn_commute i j hij T S)
  simpa only [List.map_ofFn, Function.comp_def] using hh

@[simp] theorem tensorColumns_one {h k : ℕ} :
    tensorColumns (h := h) k 1 = 1 := by
  simp [tensorColumns]

/-- A factor for one residual direction: its kernel acts across every column. -/
noncomputable def vectorFactor {h : ℕ} (k : ℕ) (g : ZMod 4 × BinaryWalsh.Address h) : Operator h k :=
  (List.ofFn (fun j : Fin k => columnKernel j g.1 g.2)).prod

/-- Concrete column kernels can be regrouped into exactly one factor per vector. -/
theorem tensorColumns_kernel_prod {h k : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h)) :
    tensorColumns k (gs.map (fun g => kernel g.1 g.2)).prod =
      (gs.map (vectorFactor k)).prod := by
  unfold tensorColumns vectorFactor
  simp only [liftColumn_prod, List.map_map, Function.comp_def, liftColumn_kernel]
  have hh := prod_rectangle (List.ofFn (fun j : Fin k => j)) gs
    (fun j g => columnKernel j g.1 g.2)
    (fun i g j g' => columnKernel_commute i j g.1 g'.1 g.2 g'.2)
  simpa only [List.map_ofFn, Function.comp_def] using hh

/-- The commutative single-column kernels also realize a left-associated product. -/
theorem kernel_prod_eq_frame {h : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h)) :
    (gs.map (fun g => kernel g.1 g.2)).prod = (frame (listPhase gs)).toLinearMap := by
  apply LinearMap.ext
  intro f
  induction gs generalizing f with
  | nil =>
    change f = frame (fun _ => 0) f
    exact (frame_zero f).symm
  | cons g gs ih =>
    rcases g with ⟨q, v⟩
    change kernel q v ((gs.map (fun g => kernel g.1 g.2)).prod f) = _
    rw [ih, ← phase_kernel_conjugation]
    change frame (fun x => q * bitLift (Labels.binary h v x)) (frame (listPhase gs) f) = _
    rw [frame_add]
    change frame (listPhase gs + (fun x => q * bitLift (Labels.binary h v x))) f =
      frame ((fun x => q * bitLift (Labels.binary h v x)) + listPhase gs) f
    rw [add_comm]

/-- The actual whole-array edge factors by residual direction whenever the
single-column edge is realized by the supplied kernel list. -/
theorem edge_factor_product {h k : ℕ} (q r : BinaryWalsh.Address h → ZMod 4)
    (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (he : ∀ f, frame r ((frame q).symm f) = kernelRun gs f) :
    tensorColumns k (frame r).toLinearMap * tensorColumns k (frame q).symm.toLinearMap =
      (gs.map (vectorFactor k)).prod := by
  have hop : (frame r).toLinearMap * (frame q).symm.toLinearMap =
      (gs.map (fun g => kernel g.1 g.2)).prod := by
    rw [kernel_prod_eq_frame]
    apply LinearMap.ext
    intro f
    change frame r ((frame q).symm f) = frame (listPhase gs) f
    rw [he, kernelRun_eq_frame]
  rw [← tensorColumns_mul, hop, tensorColumns_kernel_prod]

/-- A nested nondegenerate edge on `k` binary columns consists of exactly the
residual dimension many all-column factors. Each factor uses a single residual
vector and the forward or inverse two-term kernel in every column. The reverse
edge uses the same list with signs negated. -/
theorem exists_edge_factors {h k : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1) :
    ∃ gs : List (ZMod 4 × BinaryWalsh.Address h),
      (gs.map (vectorFactor k)).length = finrank (ZMod 2) V - finrank (ZMod 2) U ∧
      (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
      (tensorColumns k (frame (fun x => weightPhase
          (ProjectionRank.project (Labels.binary h) hs V hv x))).toLinearMap *
        tensorColumns k (frame (fun x => weightPhase
          (ProjectionRank.project (Labels.binary h) hs U hu x))).symm.toLinearMap =
        (gs.map (vectorFactor k)).prod) ∧
      (tensorColumns k (frame (fun x => weightPhase
          (ProjectionRank.project (Labels.binary h) hs U hu x))).toLinearMap *
        tensorColumns k (frame (fun x => weightPhase
          (ProjectionRank.project (Labels.binary h) hs V hv x))).symm.toLinearMap =
        ((negateKernels gs).map (vectorFactor k)).prod) := by
  obtain ⟨gs, hlen, hsigns, hfwd, hrev⟩ := exists_edge_kernels hs U V hu hv hUV hunit
  exact ⟨gs, by simpa only [List.length_map] using hlen, hsigns,
    edge_factor_product _ _ gs hfwd, edge_factor_product _ _ (negateKernels gs) hrev⟩

end IntegerMultBounds.Networks.BinaryColumns
