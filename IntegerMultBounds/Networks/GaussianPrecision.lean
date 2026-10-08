import IntegerMultBounds.Networks.GaussianDyadic

/-! Concrete integer numerator bounds for the actual binary translation
kernels and their column products. These bounds concern exact arithmetic;
they do not assert a tape implementation or charge arithmetic as one step. -/

namespace IntegerMultBounds.Networks.GaussianPrecision

open BinaryPhase BinaryWalsh

/-- A Gaussian dyadic grid point with both integer numerators bounded. -/
def BoundedGrid (n M : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℤ, z * (2 : ℂ) ^ n = (a : ℂ) + (b : ℂ) * Complex.I ∧
    |a| ≤ (M : ℤ) ∧ |b| ≤ (M : ℤ)

theorem to_grid {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) : GaussianDyadic.Grid n z := by
  obtain ⟨a, b, he, _, _⟩ := hz
  exact ⟨a, b, he⟩

theorem bounded_zero (n M : ℕ) : BoundedGrid n M 0 := ⟨0, 0, by simp⟩

theorem bounded_int (a : ℤ) (M : ℕ) (ha : |a| ≤ (M : ℤ)) :
    BoundedGrid 0 M (a : ℂ) := ⟨a, 0, by simp [ha]⟩

theorem bound_mono {n M N : ℕ} {z : ℂ} (hMN : M ≤ N) (hz : BoundedGrid n M z) :
    BoundedGrid n N z := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  exact ⟨a, b, he, ha.trans (Int.ofNat_le.mpr hMN), hb.trans (Int.ofNat_le.mpr hMN)⟩

theorem bounded_add {n M N : ℕ} {z w : ℂ}
    (hz : BoundedGrid n M z) (hw : BoundedGrid n N w) : BoundedGrid n (M + N) (z + w) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  obtain ⟨c, d, hf, hc, hd⟩ := hw
  refine ⟨a + c, b + d, ?_, ?_, ?_⟩
  · push_cast
    rw [add_mul, he, hf]
    ring
  · calc
      |a + c| ≤ |a| + |c| := abs_add_le a c
      _ ≤ (M + N : ℕ) := by push_cast; omega
  · calc
      |b + d| ≤ |b| + |d| := abs_add_le b d
      _ ≤ (M + N : ℕ) := by push_cast; omega

theorem bounded_neg {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) : BoundedGrid n M (-z) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  refine ⟨-a, -b, ?_, by simpa using ha, by simpa using hb⟩
  push_cast
  rw [neg_mul, he]
  ring

theorem bounded_sub {n M N : ℕ} {z w : ℂ}
    (hz : BoundedGrid n M z) (hw : BoundedGrid n N w) : BoundedGrid n (M + N) (z - w) := by
  simpa only [sub_eq_add_neg] using bounded_add hz (bounded_neg hw)

/-- Multiplication by the imaginary unit only permutes and negates numerators. -/
theorem bounded_I_mul {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M (Complex.I * z) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  refine ⟨-b, a, ?_, by simpa using hb, ha⟩
  rw [mul_assoc, he]
  push_cast
  calc
    _ = (a : ℂ) * Complex.I + (b : ℂ) * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- Every fourth-root phase preserves both numerator bounds. -/
theorem bounded_phase_mul {n M : ℕ} (q : ZMod 4) {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M (phase q * z) := by
  fin_cases q
  · change BoundedGrid n M (Complex.I ^ 0 * z)
    simpa using hz
  · change BoundedGrid n M (Complex.I ^ 1 * z)
    simpa using bounded_I_mul hz
  · change BoundedGrid n M (Complex.I ^ 2 * z)
    simpa only [Complex.I_sq, neg_one_mul] using bounded_neg hz
  · change BoundedGrid n M (Complex.I ^ 3 * z)
    convert bounded_neg (bounded_I_mul hz) using 1
    norm_num [pow_succ, Complex.I_mul_I]

/-- Halving increases the denominator exponent but leaves the numerators intact. -/
theorem bounded_half {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid (n + 1) M (z / 2) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  refine ⟨a, b, ?_, ha, hb⟩
  rw [pow_succ, show z / 2 * (2 ^ n * 2) = z * 2 ^ n by ring, he]

/-- A kernel sums two inputs and a phase times their difference, then halves.
The four summands give a uniform numerator bound for every phase. -/
theorem bounded_kernel_value {n M : ℕ} (q : ZMod 4) {z w : ℂ}
    (hz : BoundedGrid n M z) (hw : BoundedGrid n M w) :
    BoundedGrid (n + 1) (4 * M)
      (((1 + phase q) / 2) * z + ((1 - phase q) / 2) * w) := by
  convert bounded_half (bounded_add (bounded_add hz hw)
    (bounded_phase_mul q (bounded_sub hz hw))) using 1 <;> ring

theorem bounded_kernel {h n M : ℕ} (q : ZMod 4) (v : BinaryWalsh.Address h)
    (f : BinaryWalsh.Arrays h) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + 1) (4 * M) (kernel q v f x) := by
  intro x
  exact bounded_kernel_value q (hf x) (hf (x + v))

/-- Growth along the actual recursive list of translation kernels. -/
theorem bounded_kernelRun {h n M : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryWalsh.Arrays h) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + gs.length) (M * 4 ^ gs.length) (kernelRun gs f x) := by
  induction gs generalizing n M f with
  | nil => simpa only [kernelRun, List.length_nil, Nat.add_zero, pow_zero, mul_one] using hf
  | cons g gs ih =>
    simpa only [kernelRun, List.length_cons, Nat.add_assoc, Nat.add_comm 1, pow_succ,
      mul_assoc, mul_comm, mul_left_comm] using
      ih (kernel g.1 g.2 f) (bounded_kernel g.1 g.2 f hf)

theorem bounded_columnKernel {h k n M : ℕ} (j : Fin k) (q : ZMod 4)
    (v : BinaryWalsh.Address h) (f : BinaryColumns.Arrays h k)
    (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + 1) (4 * M) (BinaryColumns.columnKernel j q v f x) := by
  intro x
  exact bounded_kernel_value q (hf x) (hf (BinaryColumns.shift j v x))

/-- Composition propagates both the common scale and integer numerator bounds. -/
theorem bounded_operator_prod {ι : Type*} (ts : List ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)))
    (d : ℕ) (ht : ∀ T ∈ ts, ∀ n M f, (∀ x, BoundedGrid n M (f x)) →
      ∀ x, BoundedGrid (n + d) (M * 4 ^ d) (T f x))
    (n M : ℕ) (f : ι → ℂ) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + ts.length * d) (M * 4 ^ (ts.length * d)) (ts.prod f x) := by
  induction ts with
  | nil => simpa using hf
  | cons T ts ih =>
    have hs := ih (by intro S hS; exact ht S (List.mem_cons_of_mem T hS))
    have hT := ht T (List.mem_cons_self ..) (n + ts.length * d)
      (M * 4 ^ (ts.length * d)) (ts.prod f) hs
    simpa only [List.prod_cons, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_assoc, Module.End.mul_apply, pow_add, mul_assoc] using hT

/-- A factor on k actual columns has numerator growth at most four to k. -/
theorem bounded_vectorFactor {h k n M : ℕ} (g : ZMod 4 × BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + k) (M * 4 ^ k) (BinaryColumns.vectorFactor k g f x) := by
  have hh := bounded_operator_prod
    (List.ofFn (fun j : Fin k => BinaryColumns.columnKernel j g.1 g.2)) 1
    (fun T hT n M f hf => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      simpa only [pow_one, mul_comm] using bounded_columnKernel j g.1 g.2 f hf) n M f hf
  simpa only [List.length_ofFn, Nat.mul_one, BinaryColumns.vectorFactor] using hh

/-- The full factor product has an explicit power-of-four numerator bound. -/
theorem bounded_factor_product {h k n M : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + gs.length * k) (M * 4 ^ (gs.length * k))
      ((gs.map (BinaryColumns.vectorFactor k)).prod f x) := by
  have hh := bounded_operator_prod (gs.map (BinaryColumns.vectorFactor k)) k
    (fun T hT n M f hf => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hT
      exact bounded_vectorFactor g f hf) n M f hf
  simpa only [List.length_map] using hh

/-- The same concrete bounds hold for the actual Walsh-conjugated array frame. -/
theorem bounded_tensor_frame {h k n M : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address h))
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, BoundedGrid n M (f x)) :
    ∀ x, BoundedGrid (n + gs.length * k) (M * 4 ^ (gs.length * k))
      (BinaryColumns.tensorColumns k (frame (listPhase gs)).toLinearMap f x) := by
  rw [← BinaryColumns.kernel_prod_eq_frame, BinaryColumns.tensorColumns_kernel_prod]
  exact bounded_factor_product gs f hf

/-- Every nested binary projection edge, in both directions, has a denominator
and numerator bound in terms of its actual residual dimension. The residual's zero-or-unit
condition is explicit; concrete motif geometries discharge it separately. -/
theorem bounded_projection_edges {h k n M : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1)
    (f : BinaryColumns.Arrays h k) (hf : ∀ x, BoundedGrid n M (f x)) :
    let T := BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs V hv x))).toLinearMap *
      BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs U hu x))).symm.toLinearMap
    let S := BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs U hu x))).toLinearMap *
      BinaryColumns.tensorColumns k (frame (fun x => weightPhase
      (ProjectionRank.project (Labels.binary h) hs V hv x))).symm.toLinearMap
    (∀ x, BoundedGrid (n + (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k)
      (M * 4 ^ ((Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k)) (T f x)) ∧
    (∀ x, BoundedGrid (n + (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k)
      (M * 4 ^ ((Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * k)) (S f x)) := by
  obtain ⟨gs, hlen, _, hforward, hreverse⟩ := BinaryColumns.exists_edge_factors
    (k := k) hs U V hu hv hUV hunit
  simp only [List.length_map] at hlen
  dsimp only
  rw [hforward, hreverse, ← hlen]
  exact ⟨bounded_factor_product gs f hf, by
    simpa only [negateKernels, List.length_map] using bounded_factor_product (negateKernels gs) f hf⟩


end IntegerMultBounds.Networks.GaussianPrecision
