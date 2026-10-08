import IntegerMultBounds.Networks.BinaryPhase

/-! Exact finite binary Walsh operators and their translation-kernel conjugates.
We use the unnormalized Walsh sum with its explicit inverse; conjugation is the
same as with the normalized Hadamard tensor, without introducing square roots.
No tape implementation or cost claim is made. -/

namespace IntegerMultBounds.Networks.BinaryWalsh

open Module BinaryPhase

abbrev Address (h : ℕ) := Fin h → ZMod 2
abbrev Arrays (h : ℕ) := Address h → ℂ

/-- The real-valued binary sign character, embedded in the complex scalars. -/
noncomputable def sign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := rfl
@[simp] theorem sign_one : sign 1 = -1 := rfl

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b
  · change (1 : ℂ) = 1 * 1
    ring
  · change (-1 : ℂ) = 1 * (-1)
    ring
  · change (-1 : ℂ) = (-1) * 1
    ring
  · change (1 : ℂ) = (-1) * (-1)
    ring

/-- Character indexed by the actual binary dot product. -/
noncomputable def chi {h : ℕ} (v x : Address h) : ℂ := sign (Labels.binary h v x)

@[simp] theorem chi_zero {h : ℕ} (x : Address h) : chi 0 x = 1 := by simp [chi]
@[simp] theorem chi_zero_right {h : ℕ} (v : Address h) : chi v 0 = 1 := by simp [chi]

theorem chi_symm {h : ℕ} (v x : Address h) : chi v x = chi x v := by
  rw [chi, chi, Labels.binary, Labels.form_symm]

theorem chi_add {h : ℕ} (v x y : Address h) : chi v (x + y) = chi v x * chi v y := by
  simp only [chi, map_add, sign_add]

theorem chi_add_left {h : ℕ} (v w x : Address h) : chi (v + w) x = chi v x * chi w x := by
  rw [chi_symm, chi_add, chi_symm x v, chi_symm x w]

noncomputable def character {h : ℕ} (v : Address h) : AddChar (Address h) ℂ where
  toFun := chi v
  map_zero_eq_one' := chi_zero_right v
  map_add_eq_mul' := chi_add v

/-- The number of actual binary addresses. -/
def volume (h : ℕ) : ℂ := (2 : ℂ) ^ h

theorem address_card (h : ℕ) : Fintype.card (Address h) = 2 ^ h := by
  simp [Address, Fintype.card_pi]

theorem volume_ne_zero (h : ℕ) : volume h ≠ 0 := pow_ne_zero _ (by norm_num)

/-- The complete character sum vanishes for every nonzero binary frequency. -/
theorem chi_sum {h : ℕ} (v : Address h) :
    (∑ x, chi v x) = if v = 0 then volume h else 0 := by
  classical
  by_cases hv : v = 0
  · subst v
    simp [volume]
  · simp only [hv, ↓reduceIte]
    change ∑ x, character v x = 0
    apply AddChar.sum_eq_zero_iff_ne_zero.mpr
    intro hc
    have hi : ∃ i, v i ≠ 0 := by
      by_contra! hall
      exact hv (funext hall)
    obtain ⟨i, hi⟩ := hi
    have hs : chi v (Pi.single i 1) = -1 := by
      simp [chi, Labels.binary, Labels.form_single, sign, hi]
    have hh := congrArg (fun ψ : AddChar (Address h) ℂ => ψ (Pi.single i 1)) hc
    change chi v (Pi.single i 1) = 1 at hh
    rw [hs] at hh
    norm_num at hh

private theorem address_neg {h : ℕ} (v : Address h) : -v = v := by
  funext i
  exact ZMod.neg_eq_self_mod_two (v i)

theorem chi_orthogonality {h : ℕ} (x z : Address h) :
    (∑ y, chi x y * chi y z) = if x = z then volume h else 0 := by
  have ht (y : Address h) : chi x y * chi y z = chi (x + z) y := by
    rw [chi_symm y z, ← chi_add_left]
  simp_rw [ht]
  simp [chi_sum, add_eq_zero_iff_eq_neg, address_neg]

/-- The unnormalized, explicitly finite Walsh transform. -/
noncomputable def walsh (h : ℕ) : Arrays h →ₗ[ℂ] Arrays h where
  toFun f x := ∑ y, chi x y * f y
  map_add' f g := by ext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' t f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

@[simp] theorem walsh_apply {h : ℕ} (f : Arrays h) (x : Address h) :
    walsh h f x = ∑ y, chi x y * f y := rfl

/-- Exact orthogonality gives the square of Walsh as address-count times identity. -/
theorem walsh_square {h : ℕ} (f : Arrays h) (x : Address h) :
    walsh h (walsh h f) x = volume h * f x := by
  classical
  calc
    walsh h (walsh h f) x = ∑ z, (∑ y, chi x y * chi y z) * f z := by
      simp only [walsh_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ z, (if x = z then volume h else 0) * f z := by simp only [chi_orthogonality]
    _ = volume h * f x := by simp

/-- Explicit inverse normalization for the finite Walsh sum. -/
noncomputable def walshEquiv (h : ℕ) : Arrays h ≃ₗ[ℂ] Arrays h :=
  { walsh h with
    invFun := fun f => (volume h)⁻¹ • walsh h f
    left_inv := by
      intro f
      ext x
      change (volume h)⁻¹ * walsh h (walsh h f) x = f x
      rw [walsh_square]
      rw [← mul_assoc, inv_mul_cancel₀ (volume_ne_zero h), one_mul]
    right_inv := by
      intro f
      ext x
      change walsh h ((volume h)⁻¹ • walsh h f) x = f x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, walsh_square]
      rw [← mul_assoc, inv_mul_cancel₀ (volume_ne_zero h), one_mul] }

@[simp] theorem walsh_inverse {h : ℕ} (f : Arrays h) :
    walsh h ((walshEquiv h).symm f) = f := (walshEquiv h).apply_symm_apply f

/-- Translate actual array addresses by the indicated binary vector. -/
noncomputable def translation {h : ℕ} (v : Address h) : Arrays h →ₗ[ℂ] Arrays h where
  toFun f x := f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def characterMultiply {h : ℕ} (v : Address h) : Arrays h →ₗ[ℂ] Arrays h where
  toFun f x := chi v x * f x
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' t f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Walsh sends character multiplication to actual address translation. -/
theorem walsh_character {h : ℕ} (v : Address h) (f : Arrays h) :
    walsh h (characterMultiply v f) = translation v (walsh h f) := by
  ext x
  change (∑ y, chi x y * (chi v y * f y)) = ∑ y, chi (x + v) y * f y
  simp only [chi_add_left, mul_assoc]

/-- Exact conjugation, including the inverse normalization. -/
theorem character_conjugation {h : ℕ} (v : Address h) (f : Arrays h) :
    walsh h (characterMultiply v ((walshEquiv h).symm f)) = translation v f := by
  rw [walsh_character, walsh_inverse]

/-- The genuine translation kernel corresponding to one binary direction. -/
noncomputable def kernel {h : ℕ} (q : ZMod 4) (v : Address h) : Arrays h →ₗ[ℂ] Arrays h :=
  ((1 + phase q) / 2) • LinearMap.id + ((1 - phase q) / 2) • translation v

@[simp] theorem kernel_apply {h : ℕ} (q : ZMod 4) (v : Address h) (f : Arrays h) (x : Address h) :
    kernel q v f x = ((1 + phase q) / 2) * f x + ((1 - phase q) / 2) * f (x + v) := rfl

/-- A rank-one phase conjugates to precisely the two-term translation kernel. -/
theorem phase_kernel_conjugation {h : ℕ} (q : ZMod 4) (v : Address h) (f : Arrays h) :
    walsh h (phaseDiagonal (fun x => q * bitLift (Labels.binary h v x)) ((walshEquiv h).symm f)) =
      kernel q v f := by
  have hd (g : Arrays h) : phaseDiagonal (fun x => q * bitLift (Labels.binary h v x)) g =
      ((1 + phase q) / 2) • g + ((1 - phase q) / 2) • characterMultiply v g := by
    ext x
    change phase (q * bitLift (Labels.binary h v x)) * g x =
      ((1 + phase q) / 2) * g x + ((1 - phase q) / 2) * (chi v x * g x)
    rw [phase_bit]
    dsimp [chi, sign]
    ring
  rw [hd, map_add, map_smul, map_smul, walsh_character, walsh_inverse]
  rfl

/-- The manuscript's forward Gaussian-dyadic coefficients. -/
theorem kernel_forward {h : ℕ} (v : Address h) (f : Arrays h) (x : Address h) :
    kernel 1 v f x = ((1 + Complex.I) / 2) * f x + ((1 - Complex.I) / 2) * f (x + v) := by
  rw [kernel_apply, phase_one]

theorem phase_neg_one : phase (-1) = -Complex.I := by
  change Complex.I ^ 3 = -Complex.I
  norm_num [pow_succ, Complex.I_mul_I]

/-- The inverse-phase kernel exchanges the two manuscript coefficients. -/
theorem kernel_backward {h : ℕ} (v : Address h) (f : Arrays h) (x : Address h) :
    kernel (-1) v f x = ((1 - Complex.I) / 2) * f x + ((1 + Complex.I) / 2) * f (x + v) := by
  rw [kernel_apply, phase_neg_one]
  ring

/-- A complete phase frame, conjugated by the finite Walsh equivalence. -/
noncomputable def frame {h : ℕ} (q : Address h → ZMod 4) : Arrays h ≃ₗ[ℂ] Arrays h :=
  ((walshEquiv h).symm.trans (phaseDiagonal q)).trans (walshEquiv h)

@[simp] theorem frame_apply {h : ℕ} (q : Address h → ZMod 4) (f : Arrays h) :
    frame q f = walsh h (phaseDiagonal q ((walshEquiv h).symm f)) := rfl

theorem frame_zero {h : ℕ} (f : Arrays h) : frame (fun _ => 0) f = f := by
  rw [frame_apply]
  have hd (g : Arrays h) : phaseDiagonal (fun _ => (0 : ZMod 4)) g = g := by
    ext x
    change phase 0 * g x = g x
    rw [phase_zero, one_mul]
  rw [hd, walsh_inverse]

theorem frame_add {h : ℕ} (q r : Address h → ZMod 4) (f : Arrays h) :
    frame r (frame q f) = frame (q + r) f := by
  change walshEquiv h (phaseDiagonal r ((walshEquiv h).symm
    (walshEquiv h (phaseDiagonal q ((walshEquiv h).symm f))))) =
      walshEquiv h (phaseDiagonal (q + r) ((walshEquiv h).symm f))
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg (walshEquiv h)
  exact congrArg (fun e : Arrays h ≃ₗ[ℂ] Arrays h => e ((walshEquiv h).symm f))
    (phaseDiagonal_trans q r)

/-- Actual edge composition subtracts the source phase from the target phase. -/
theorem frame_edge {h : ℕ} (q r : Address h → ZMod 4) (f : Arrays h) :
    frame r ((frame q).symm f) = frame (r - q) f := by
  change walshEquiv h (phaseDiagonal r ((walshEquiv h).symm
    (walshEquiv h ((phaseDiagonal q).symm ((walshEquiv h).symm f))))) =
      walshEquiv h (phaseDiagonal (r - q) ((walshEquiv h).symm f))
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg (walshEquiv h)
  ext x
  change phase (r x) * (phase (-q x) * (walshEquiv h).symm f x) =
    phase (r x - q x) * (walshEquiv h).symm f x
  rw [← mul_assoc, ← phase_add, sub_eq_add_neg]

/-- Run the explicitly supplied finite sequence of translation kernels. -/
noncomputable def kernelRun {h : ℕ} : List (ZMod 4 × Address h) → Arrays h → Arrays h
  | [], f => f
  | (q, v) :: gs, f => kernelRun gs (kernel q v f)

def listPhase {h : ℕ} : List (ZMod 4 × Address h) → Address h → ZMod 4
  | [] => 0
  | (q, v) :: gs => (fun x => q * bitLift (Labels.binary h v x)) + listPhase gs

/-- Literal finite kernel composition equals the corresponding full frame. -/
theorem kernelRun_eq_frame {h : ℕ} (gs : List (ZMod 4 × Address h)) (f : Arrays h) :
    kernelRun gs f = frame (listPhase gs) f := by
  induction gs generalizing f with
  | nil => exact (frame_zero f).symm
  | cons g gs ih =>
    rcases g with ⟨q, v⟩
    rw [kernelRun, ih, ← phase_kernel_conjugation]
    exact frame_add _ _ f

theorem listPhase_ofFn {h d : ℕ} (g : Fin d → ZMod 4 × Address h) (x : Address h) :
    listPhase (List.ofFn g) x = ∑ i, (g i).1 * bitLift (Labels.binary h (g i).2 x) := by
  have hl (gs : List (ZMod 4 × Address h)) : listPhase gs x =
      (gs.map fun p => p.1 * bitLift (Labels.binary h p.2 x)).sum := by
    induction gs with
    | nil => rfl
    | cons p gs ih => rcases p with ⟨q, v⟩; simpa [listPhase] using congrArg (fun z => q * bitLift (Labels.binary h v x) + z) ih
  rw [hl, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The edge's actual finite kernel list, one entry per residual basis vector. -/
noncomputable def edgeKernels {h d : ℕ} {W : Submodule (ZMod 2) (Address h)} (b : Basis (Fin d) (ZMod 2) W) :
    List (ZMod 4 × Address h) := List.ofFn fun i => (weightPhase (b i : Address h), (b i : Address h))

@[simp] theorem edgeKernels_length {h d : ℕ} {W : Submodule (ZMod 2) (Address h)}
    (b : Basis (Fin d) (ZMod 2) W) : (edgeKernels b).length = d := List.length_ofFn

theorem edgeKernels_signs {h d : ℕ} {W : Submodule (ZMod 2) (Address h)}
    (b : Basis (Fin d) (ZMod 2) W)
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0) :
    ∀ g ∈ edgeKernels b, g.1 = 1 ∨ g.1 = -1 := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact unit_weightPhase _ (by simpa using hgram i i)

/-- The entire phase-frame edge is a literal sequence of exactly `d` translation
kernels with the manuscript's forward/inverse coefficients. -/
theorem edge_kernel_product {h d : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (b : Basis (Fin d) (ZMod 2) (ProjectionRank.residual (Labels.binary h) U V))
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0) (f : Arrays h) :
    frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs V hv x))
      ((frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs U hu x))).symm f) =
      kernelRun (edgeKernels b) f := by
  rw [frame_edge, kernelRun_eq_frame]
  congr 1
  apply congrArg frame
  funext x
  simp only [Pi.sub_apply, edgeKernels, listPhase_ofFn]
  rw [weightPhase_difference hs U V hu hv hUV]
  exact weightPhase_project hs _ _ b hgram x

/-- Negating the phase gives the actual inverse translation kernel. -/
theorem kernel_inverse {h : ℕ} (q : ZMod 4) (v : Address h) (f : Arrays h) :
    kernel (-q) v (kernel q v f) = f := by
  change kernelRun [(q, v), (-q, v)] f = f
  rw [kernelRun_eq_frame]
  have hz : listPhase [(q, v), (-q, v)] = 0 := by
    funext x
    simp [listPhase, neg_mul]
  rw [hz]
  exact frame_zero f

/-- The decreasing-edge list reverses every phase sign. Its scalar kernels
commute because their common diagonalization is proved above. -/
def negateKernels {h : ℕ} (gs : List (ZMod 4 × Address h)) : List (ZMod 4 × Address h) :=
  gs.map fun p => (-p.1, p.2)

theorem listPhase_negate {h : ℕ} (gs : List (ZMod 4 × Address h)) :
    listPhase (negateKernels gs) = -listPhase gs := by
  induction gs with
  | nil => simp [negateKernels, listPhase]
  | cons p gs ih =>
    rcases p with ⟨q, v⟩
    funext x
    simp only [negateKernels, List.map_cons, listPhase, Pi.add_apply, Pi.neg_apply] at *
    rw [congrFun ih x]
    simp only [Pi.neg_apply]
    ring

theorem edge_kernel_product_reverse {h d : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (b : Basis (Fin d) (ZMod 2) (ProjectionRank.residual (Labels.binary h) U V))
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0) (f : Arrays h) :
    frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs U hu x))
      ((frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs V hv x))).symm f) =
      kernelRun (negateKernels (edgeKernels b)) f := by
  rw [frame_edge, kernelRun_eq_frame, listPhase_negate]
  congr 1
  apply congrArg frame
  funext x
  simp only [Pi.sub_apply, Pi.neg_apply, edgeKernels, listPhase_ofFn]
  rw [← weightPhase_project hs _ (ProjectionRank.residual_nondegenerate (Labels.binary h) hs U V hu hv hUV) b hgram x,
    ← weightPhase_difference hs U V hu hv hUV]
  abel

/-- A complete scalar edge realization: its literal number of forward/inverse
translation factors is exactly the residual dimension difference. Nonzero
residuals must supply their actual norm-one witness. -/
theorem exists_edge_kernels {h : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1) :
    ∃ gs : List (ZMod 4 × Address h),
      gs.length = finrank (ZMod 2) V - finrank (ZMod 2) U ∧
      (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
      (∀ f, frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs V hv x))
        ((frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs U hu x))).symm f) =
          kernelRun gs f) ∧
      (∀ f, frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs U hu x))
        ((frame (fun x => weightPhase (ProjectionRank.project (Labels.binary h) hs V hv x))).symm f) =
          kernelRun (negateKernels gs) f) := by
  obtain ⟨b, hgram, _, hd⟩ := exists_difference_decomposition (Labels.binary h) hs U V hu hv hUV hunit
  refine ⟨edgeKernels b, ?_, edgeKernels_signs b hgram,
    edge_kernel_product hs U V hu hv hUV b hgram,
    edge_kernel_product_reverse hs U V hu hv hUV b hgram⟩
  rw [edgeKernels_length, hd]

end IntegerMultBounds.Networks.BinaryWalsh
