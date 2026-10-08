import IntegerMultBounds.Networks.BinaryColumns

/-! Exact arithmetic closure for the binary phase interfaces. A grid at precision
`n` consists of Gaussian integers divided by `2^n`. Each literal translation
kernel increases precision by at most one, and a whole-column factor by at most
the number of columns. These are arithmetic bounds, not tape runtimes. -/

namespace IntegerMultBounds.Networks.GaussianDyadic

open BinaryPhase BinaryWalsh

/-- A complex number with two integer numerators and a common binary scale. -/
def Grid (n : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℤ, z * (2 : ℂ) ^ n = (a : ℂ) + (b : ℂ) * Complex.I

theorem grid_zero (n : ℕ) : Grid n 0 := ⟨0, 0, by simp⟩

theorem grid_int (a : ℤ) : Grid 0 (a : ℂ) := ⟨a, 0, by simp⟩

theorem grid_I : Grid 0 Complex.I := ⟨0, 1, by simp⟩

theorem grid_add {n : ℕ} {z w : ℂ} (hz : Grid n z) (hw : Grid n w) : Grid n (z + w) := by
  obtain ⟨a, b, ha⟩ := hz
  obtain ⟨c, d, hc⟩ := hw
  refine ⟨a + c, b + d, ?_⟩
  push_cast
  rw [add_mul, ha, hc]
  ring

theorem grid_neg {n : ℕ} {z : ℂ} (hz : Grid n z) : Grid n (-z) := by
  obtain ⟨a, b, ha⟩ := hz
  refine ⟨-a, -b, ?_⟩
  push_cast
  rw [neg_mul, ha]
  ring

theorem grid_sub {n : ℕ} {z w : ℂ} (hz : Grid n z) (hw : Grid n w) : Grid n (z - w) := by
  simpa only [sub_eq_add_neg] using grid_add hz (grid_neg hw)

theorem grid_mul {n m : ℕ} {z w : ℂ} (hz : Grid n z) (hw : Grid m w) :
    Grid (n + m) (z * w) := by
  obtain ⟨a, b, ha⟩ := hz
  obtain ⟨c, d, hc⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  rw [pow_add, show z * w * (2 ^ n * 2 ^ m) = (z * 2 ^ n) * (w * 2 ^ m) by ring, ha, hc]
  push_cast
  calc
    _ = (a : ℂ) * c + ((a : ℂ) * d + (b : ℂ) * c) * Complex.I +
        (b : ℂ) * d * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem grid_half {n : ℕ} {z : ℂ} (hz : Grid n z) : Grid (n + 1) (z / 2) := by
  obtain ⟨a, b, ha⟩ := hz
  refine ⟨a, b, ?_⟩
  rw [pow_succ, show z / 2 * (2 ^ n * 2) = z * 2 ^ n by ring, ha]

theorem grid_mono {n m : ℕ} {z : ℂ} (hnm : n ≤ m) (hz : Grid n z) : Grid m z := by
  obtain ⟨a, b, ha⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine ⟨a * 2 ^ d, b * 2 ^ d, ?_⟩
  rw [pow_add, ← mul_assoc, ha]
  push_cast
  ring

/-- All four phase values are Gaussian integers. -/
theorem grid_phase (q : ZMod 4) : Grid 0 (phase q) := by
  fin_cases q
  · change Grid 0 (Complex.I ^ 0)
    simpa using grid_int 1
  · change Grid 0 (Complex.I ^ 1)
    simpa using grid_I
  · change Grid 0 (Complex.I ^ 2)
    simpa only [Complex.I_sq, Int.cast_neg, Int.cast_one] using grid_int (-1)
  · change Grid 0 (Complex.I ^ 3)
    convert grid_neg grid_I using 1
    norm_num [pow_succ, Complex.I_mul_I]

/-- The literal two-term kernel uses only exact Gaussian integer arithmetic
and one division by two, independently of the address dimension. -/
theorem grid_kernel_value {n : ℕ} (q : ZMod 4) {z w : ℂ}
    (hz : Grid n z) (hw : Grid n w) :
    Grid (n + 1) (((1 + phase q) / 2) * z + ((1 - phase q) / 2) * w) := by
  have hphase : Grid n (phase q * (z - w)) := by
    simpa only [Nat.zero_add] using grid_mul (grid_phase q) (grid_sub hz hw)
  convert grid_half (grid_add (grid_add hz hw) hphase) using 1
  ring

theorem grid_kernel {h n : ℕ} (q : ZMod 4) (v : BinaryWalsh.Address h)
    (f : BinaryWalsh.Arrays h) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + 1) (kernel q v f x) := by
  intro x
  exact grid_kernel_value q (hf x) (hf (x + v))

/-- A concrete one-column edge list loses at most one binary place per factor. -/
theorem grid_kernelRun {h n : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryWalsh.Arrays h) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + gs.length) (kernelRun gs f x) := by
  induction gs generalizing n f with
  | nil => simpa only [kernelRun, List.length_nil, Nat.add_zero] using hf
  | cons g gs ih =>
    simpa only [kernelRun, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
      ih (kernel g.1 g.2 f) (grid_kernel g.1 g.2 f hf)

theorem grid_columnKernel {h k n : ℕ} (j : Fin k) (q : ZMod 4)
    (v : BinaryWalsh.Address h) (f : BinaryColumns.Arrays h k)
    (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + 1) (BinaryColumns.columnKernel j q v f x) := by
  intro x
  exact grid_kernel_value q (hf x) (hf (BinaryColumns.shift j v x))

/-- Composition charges the actual supplied per-operator precision increments. -/
theorem grid_operator_prod {ι : Type*} (ts : List ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)))
    (d : ℕ) (ht : ∀ T ∈ ts, ∀ n f, (∀ x, Grid n (f x)) → ∀ x, Grid (n + d) (T f x))
    (n : ℕ) (f : ι → ℂ) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + ts.length * d) (ts.prod f x) := by
  induction ts with
  | nil => simpa using hf
  | cons T ts ih =>
    have hs := ih (by intro S hS; exact ht S (List.mem_cons_of_mem T hS))
    have hT := ht T (List.mem_cons_self ..) (n + ts.length * d) (ts.prod f) hs
    simpa only [List.prod_cons, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_assoc, Module.End.mul_apply] using hT

theorem grid_vectorFactor {h k n : ℕ} (g : ZMod 4 × BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + k) (BinaryColumns.vectorFactor k g f x) := by
  have hh := grid_operator_prod (List.ofFn (fun j : Fin k => BinaryColumns.columnKernel j g.1 g.2)) 1
    (fun T hT n f hf => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      exact grid_columnKernel j g.1 g.2 f hf) n f hf
  simpa only [List.length_ofFn, Nat.mul_one, BinaryColumns.vectorFactor] using hh

/-- The full regrouped binary interface has an explicit common denominator:
at most `k` new binary places per residual direction. -/
theorem grid_factor_product {h k n : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + gs.length * k) ((gs.map (BinaryColumns.vectorFactor k)).prod f x) := by
  have hh := grid_operator_prod (gs.map (BinaryColumns.vectorFactor k)) k
    (fun T hT n f hf => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hT
      exact grid_vectorFactor g f hf) n f hf
  simpa only [List.length_map] using hh

/-- Precision control applies to the actual Walsh-conjugated array frame. -/
theorem grid_tensor_frame {h k n : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, Grid n (f x)) :
    ∀ x, Grid (n + gs.length * k)
      (BinaryColumns.tensorColumns k (frame (listPhase gs)).toLinearMap f x) := by
  rw [← BinaryColumns.kernel_prod_eq_frame, BinaryColumns.tensorColumns_kernel_prod]
  exact grid_factor_product gs f hf

/-- Every nested binary projection edge, in both directions, has a denominator
bound in terms of its actual residual dimension. The residual's zero-or-unit
condition is explicit; concrete motif geometries discharge it separately. -/
theorem grid_projection_edges {h k n : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, Grid n (f x)) :
    let T := BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs V hv x))).toLinearMap *
      BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs U hu x))).symm.toLinearMap
    let S := BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs U hu x))).toLinearMap *
      BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs V hv x))).symm.toLinearMap
    (∀ x, Grid (n + (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k) (T f x)) ∧
    (∀ x, Grid (n + (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k) (S f x)) := by
  obtain ⟨gs, hlen, _, hforward, hreverse⟩ := BinaryColumns.exists_edge_factors
    (k := k) hs U V hu hv hUV hunit
  simp only [List.length_map] at hlen
  dsimp only
  rw [hforward, hreverse, ← hlen]
  exact ⟨grid_factor_product gs f hf, by
    simpa only [negateKernels, List.length_map] using grid_factor_product (negateKernels gs) f hf⟩

end IntegerMultBounds.Networks.GaussianDyadic
