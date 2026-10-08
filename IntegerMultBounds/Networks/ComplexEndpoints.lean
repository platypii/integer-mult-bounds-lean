import IntegerMultBounds.Networks.ComplexFramedExecution
import IntegerMultBounds.Networks.TensorTerminalWeight
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Concrete binary phase endpoint corrections for the actual complex network.
The source/sink projectors and diagonal corrections are proved as operators;
no terminal transform identity is assumed. -/

namespace IntegerMultBounds.Networks.ComplexEndpoints

open BinaryPhase BinaryWalsh
open scoped TensorProduct

section Walsh
variable {h : ℕ}

private theorem address_add_self (u : BinaryWalsh.Address h) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (u i)

/-- Translation in the Walsh input is character multiplication in its output. -/
theorem walsh_translation (u : BinaryWalsh.Address h) (f : BinaryWalsh.Arrays h) :
    walsh h (translation u f) = characterMultiply u (walsh h f) := by
  ext x
  change (∑ y, chi x y * f (y + u)) = chi u x * ∑ y, chi x y * f y
  have he := Equiv.sum_comp (Equiv.addRight u) (fun y => chi x (y + u) * f y)
  change (∑ y, chi x (y + u + u) * f (y + u)) = ∑ y, chi x (y + u) * f y at he
  simp only [add_assoc, address_add_self, add_zero] at he
  rw [he]
  simp only [chi_add, Finset.mul_sum, chi_symm x u]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The inverse Walsh normalization preserves the same translation identity. -/
theorem inverse_character (u : BinaryWalsh.Address h) (f : BinaryWalsh.Arrays h) :
    (walshEquiv h).symm (characterMultiply u f) = translation u ((walshEquiv h).symm f) := by
  apply (walshEquiv h).injective
  change walsh h ((walshEquiv h).symm (characterMultiply u f)) =
    walsh h (translation u ((walshEquiv h).symm f))
  rw [walsh_inverse, walsh_translation, walsh_inverse]

/-- Conjugating a phase frame by the physical sign character translates its
actual binary spectral phase. -/
theorem character_frame_character (u : BinaryWalsh.Address h)
    (q : BinaryWalsh.Address h → ZMod 4) (f : BinaryWalsh.Arrays h) :
    characterMultiply u (frame q (characterMultiply u f)) =
      frame (fun x => q (x + u)) f := by
  rw [frame_apply, ← walsh_translation, inverse_character]
  rw [frame_apply]
  apply congrArg (walsh h)
  ext x
  change phase (q (x + u)) * (walshEquiv h).symm f (x + u + u) =
    phase (q (x + u)) * (walshEquiv h).symm f x
  rw [add_assoc, address_add_self, add_zero]

/-- A constant spectral phase is a single scalar on the whole array. -/
theorem frame_sub_const (q : BinaryWalsh.Address h → ZMod 4) (c : ZMod 4)
    (f : BinaryWalsh.Arrays h) :
    frame (fun x => q x - c) f = phase (-c) • frame q f := by
  rw [frame_apply, frame_apply]
  have hd : phaseDiagonal (fun x => q x - c) ((walshEquiv h).symm f) =
      phase (-c) • phaseDiagonal q ((walshEquiv h).symm f) := by
    ext x
    change phase (q x - c) * (walshEquiv h).symm f x =
      phase (-c) * (phase (q x) * (walshEquiv h).symm f x)
    rw [sub_eq_add_neg, phase_add]
    ring
  rw [hd, map_smul]
end Walsh

section Projectors
variable {h : ℕ} (hs : (Labels.binary h).IsSymm)

/-- The total projector is the identity at the full terminal label. -/
theorem projector_top (x : BinaryWalsh.Address h) :
    ProjectionTrace.projector (Labels.binary h) hs ⊤ x = x := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.top_nondegenerate _ Labels.binary_nondegenerate)]
  exact ProjectionRank.project_left _ _ _ _ Submodule.mem_top

/-- The zero source label contributes no phase or address operation. -/
theorem projector_bot (x : BinaryWalsh.Address h) :
    ProjectionTrace.projector (Labels.binary h) hs ⊥ x = 0 := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.bot_nondegenerate _)]
  exact ProjectionRank.project_right _ _ _ _ (by simp)

/-- A binary norm-one terminal line has its literal rank-one projector. -/
theorem projector_line (u x : BinaryWalsh.Address h) (hu : Labels.binary h u u = 1) :
    ProjectionTrace.projector (Labels.binary h) hs ((ZMod 2) ∙ u) x = Labels.binary h u x • u := by
  have hu' : Labels.binary h u u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hn : ((Labels.binary h).restrict ((ZMod 2) ∙ u)).Nondegenerate :=
    Labels.line_nondegenerate (Labels.binary h) u hu'
  rw [ProjectionTrace.projector_eq _ _ _ hn]
  have hm : Labels.binary h u x • u ∈ (ZMod 2) ∙ u :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have ho : x - Labels.binary h u x • u ∈ (Labels.binary h).orthogonal ((ZMod 2) ∙ u) := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [map_smul, LinearMap.smul_apply, map_sub, hu, smul_eq_mul, mul_comm]
  have hp := ProjectionRank.project_right (Labels.binary h) hs ((ZMod 2) ∙ u) hn ho
  rw [map_sub, ProjectionRank.project_left (Labels.binary h) hs ((ZMod 2) ∙ u) hn hm] at hp
  exact sub_eq_zero.mp hp

/-- Complementary true projectors sum to the input binary vector. -/
theorem projector_complement (U : Submodule (ZMod 2) (BinaryWalsh.Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate) (x : BinaryWalsh.Address h) :
    ProjectionTrace.projector (Labels.binary h) hs U x +
      ProjectionTrace.projector (Labels.binary h) hs ((Labels.binary h).orthogonal U) x = x := by
  rw [ProjectionTrace.projector_eq _ _ _ hu,
    ProjectionTrace.projector_eq _ _ _ (ProjectionRank.orthogonal_nondegenerate _ hs Labels.binary_nondegenerate U hu)]
  exact congrArg (fun f : BinaryWalsh.Address h →ₗ[ZMod 2] BinaryWalsh.Address h => f x)
    (ProjectionRank.complementary_sum _ hs Labels.binary_nondegenerate U hu)

/-- The actual line-to-complement edge phase uses the line's binary dot product. -/
theorem complement_line_phase (u x : BinaryWalsh.Address h) (hu : Labels.binary h u u = 1) :
    weightPhase (ProjectionTrace.projector (Labels.binary h) hs
      ((Labels.binary h).orthogonal ((ZMod 2) ∙ u)) x) -
      weightPhase (ProjectionTrace.projector (Labels.binary h) hs ((ZMod 2) ∙ u) x) =
      weightPhase x - 2 * (bitLift (Labels.binary h u x) * weightPhase u) := by
  have hu' : Labels.binary h u u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hn : ((Labels.binary h).restrict ((ZMod 2) ∙ u)).Nondegenerate :=
    Labels.line_nondegenerate (Labels.binary h) u hu'
  let U : Submodule (ZMod 2) (BinaryWalsh.Address h) := (ZMod 2) ∙ u
  have ho : Labels.binary h (ProjectionTrace.projector (Labels.binary h) hs U x)
      (ProjectionTrace.projector (Labels.binary h) hs ((Labels.binary h).orthogonal U) x) = 0 := by
    rw [ProjectionTrace.projector_eq _ _ _ hn,
      ProjectionTrace.projector_eq _ _ _ (ProjectionRank.orthogonal_nondegenerate _ hs Labels.binary_nondegenerate U hn)]
    have hm : ProjectionRank.project (Labels.binary h) hs ((Labels.binary h).orthogonal U)
        (ProjectionRank.orthogonal_nondegenerate _ hs Labels.binary_nondegenerate U hn) x ∈
        (Labels.binary h).orthogonal U := ProjectionRank.project_mem _ _ _ _ x
    exact hm _ (ProjectionRank.project_mem _ _ U hn x)
  have hw := weightPhase_add_of_orthogonal _ _ ho
  rw [projector_complement hs U hn x] at hw
  change weightPhase x = weightPhase (ProjectionTrace.projector (Labels.binary h) hs ((ZMod 2) ∙ u) x) + _ at hw
  rw [projector_line hs u x hu, weightPhase_smul] at hw
  rw [hw, projector_line hs u x hu, weightPhase_smul]
  ring

/-- Translating the exceptional endpoint phase by its own unit direction
leaves the full phase and one constant inverse phase. -/
theorem translated_endpoint_phase (u x : BinaryWalsh.Address h) (hu : Labels.binary h u u = 1) :
    weightPhase (x + u) - 2 * (bitLift (Labels.binary h u (x + u)) * weightPhase u) =
      weightPhase x - weightPhase u := by
  rw [weightPhase_add, map_add, hu, (show (Labels.binary h).IsSymm from ⟨Labels.form_symm 0⟩).eq x u]
  change weightPhase x + weightPhase u - 2 * bitLift (Labels.binary h u x) -
    2 * (bitLift (Labels.binary h u x + 1) * weightPhase u) = _
  have ha (b : ZMod 2) (w : ZMod 4) (hw : w = 1 ∨ w = -1) :
      w - 2 * bitLift b - 2 * (bitLift (b + 1) * w) = -w := by
    rcases hw with rfl | rfl <;> fin_cases b <;> decide
  calc
    _ = weightPhase x + (weightPhase u - 2 * bitLift (Labels.binary h u x) -
        2 * (bitLift (Labels.binary h u x + 1) * weightPhase u)) := by ring
    _ = _ := by rw [ha _ _ (unit_weightPhase u hu), sub_eq_add_neg]

/-- The physical input/output sign characters and one scalar phase turn the
actual exceptional endpoint operator into the full forward weight frame. -/
theorem corrected_line_endpoint (u : BinaryWalsh.Address h) (hu : Labels.binary h u u = 1)
    (f : BinaryWalsh.Arrays h) :
    phase (weightPhase u) • characterMultiply u
      (frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs
        ((Labels.binary h).orthogonal ((ZMod 2) ∙ u)) x))
        ((frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs
          ((ZMod 2) ∙ u) x))).symm (characterMultiply u f))) = frame weightPhase f := by
  rw [frame_edge, character_frame_character]
  have hp : (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs
      ((Labels.binary h).orthogonal ((ZMod 2) ∙ u)) (x + u)) -
      weightPhase (ProjectionTrace.projector (Labels.binary h) hs ((ZMod 2) ∙ u) (x + u))) =
      fun x => weightPhase x - weightPhase u := by
    funext x
    rw [complement_line_phase hs u _ hu, translated_endpoint_phase u x hu]
  simp only [Pi.sub_apply]
  rw [hp, frame_sub_const, smul_smul]
  rw [mul_comm, phase_neg_mul, one_smul]
end Projectors
section Columns
open BinaryColumns
variable {h : ℕ}

theorem liftColumn_smul {k : ℕ} (j : Fin k) (c : ℂ)
    (T : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) :
    liftColumn j (c • T) = c • liftColumn j T := by
  ext f x
  rfl

/-- Tensoring a scalar multiple applies the scalar once per column. -/
theorem tensorColumns_smul (k : ℕ) (c : ℂ)
    (T : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h) :
    tensorColumns k (c • T) = c ^ k • tensorColumns k T := by
  unfold tensorColumns
  simp only [liftColumn_smul]
  have he := (List.smul_prod (List.ofFn (fun j : Fin k => liftColumn j T)) c).symm
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using he

/-- The correction is the tensor of the actual binary sign characters. -/
noncomputable def signColumns (k : ℕ) (u : BinaryWalsh.Address h) : Operator h k :=
  tensorColumns k (characterMultiply u)

/-- This correction is diagonal on physical joint addresses. -/
theorem signColumns_apply (k : ℕ) (u : BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) (x : BinaryColumns.Address h k) :
    signColumns k u f x = (∏ j, chi u (x j)) * f x := by
  have hcol (j : Fin k) (g : BinaryColumns.Arrays h k) :
      liftColumn j (characterMultiply u) g x = chi u (x j) * g x := by
    simp [liftColumn, characterMultiply, Function.update_eq_self]
  have hprod (js : List (Fin k)) (g : BinaryColumns.Arrays h k) :
      ((js.map (fun j => liftColumn j (characterMultiply u))).prod) g x =
        (js.map (fun j => chi u (x j))).prod * g x := by
    induction js generalizing g with
    | nil => simp
    | cons j js ih =>
      simp only [List.map_cons, List.prod_cons]
      change liftColumn j (characterMultiply u) ((js.map (fun j => liftColumn j (characterMultiply u))).prod g) x = _
      rw [hcol, ih, mul_assoc]
  have he := hprod (List.ofFn (fun j : Fin k => j)) f
  simpa only [signColumns, tensorColumns, List.map_ofFn, Function.comp_def, List.prod_ofFn] using he

/-- The desired forward tensor transform on all address bits and columns. -/
noncomputable def fullFrame (k : ℕ) : BinaryColumns.Arrays h k ≃ₗ[ℂ] BinaryColumns.Arrays h k :=
  BinaryColumnFrame.frameEquiv k weightPhase

theorem labelFrame_bot (hs : (Labels.binary h).IsSymm) (k : ℕ) :
    BinaryColumnFrame.labelFrame hs k ⊥ = LinearEquiv.refl ℂ _ := by
  have hp : (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs ⊥ x)) = 0 := by
    funext x
    rw [projector_bot, weightPhase_zero]
    rfl
  have hf : (frame (0 : BinaryWalsh.Address h → ZMod 4)).toLinearMap = 1 := by
    apply LinearMap.ext
    intro f
    exact frame_zero f
  apply LinearEquiv.toLinearMap_injective
  change tensorColumns k (frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs ⊥ x))).toLinearMap = 1
  rw [hp, hf, tensorColumns_one]

theorem labelFrame_top (hs : (Labels.binary h).IsSymm) (k : ℕ) :
    BinaryColumnFrame.labelFrame hs k ⊤ = fullFrame k := by
  have hp : (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs ⊤ x)) = weightPhase := by
    funext x
    rw [projector_top]
  unfold BinaryColumnFrame.labelFrame fullFrame
  rw [hp]

/-- The source and sink diagonal corrections produce the full forward tensor
on the exceptional line/complement route for every number of columns. -/
theorem corrected_column_endpoint (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (u : BinaryWalsh.Address h) (hu : Labels.binary h u u = 1)
    (f : BinaryColumns.Arrays h k) :
    phase (weightPhase u) ^ k • signColumns k u
      (BinaryColumnFrame.labelFrame hs k ((Labels.binary h).orthogonal ((ZMod 2) ∙ u))
        ((BinaryColumnFrame.labelFrame hs k ((ZMod 2) ∙ u)).symm (signColumns k u f))) =
      fullFrame k f := by
  have he : phase (weightPhase u) •
      (characterMultiply u *
        (frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs
          ((Labels.binary h).orthogonal ((ZMod 2) ∙ u)) x))).toLinearMap *
        (frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs
          ((ZMod 2) ∙ u) x))).symm.toLinearMap * characterMultiply u) =
      (frame weightPhase).toLinearMap := by
    apply LinearMap.ext
    intro g
    exact corrected_line_endpoint hs u hu g
  have ht := congrArg (tensorColumns k) he
  simp only [tensorColumns_smul, tensorColumns_mul] at ht
  exact congrArg (fun T : Operator h k => T f) ht
/-- One forward C kernel for each genuine binary address coordinate. -/
def coordinateKernels (h : ℕ) : List (ZMod 4 × BinaryWalsh.Address h) :=
  List.ofFn (fun j : Fin h => (1, Pi.single j 1))

theorem coordinateKernels_phase : listPhase (coordinateKernels h) = weightPhase := by
  funext x
  rw [coordinateKernels, listPhase_ofFn]
  simp [Labels.binary, Labels.form_apply, Pi.single_apply, weightPhase]

/-- The full weight frame is precisely the forward C tensor: one forward
coordinate kernel on every binary bit, tensoring the same operator across
all columns. This identifies the target without a transform assumption. -/
theorem fullFrame_coordinate_product (k : ℕ) :
    (fullFrame (h := h) k).toLinearMap =
      ((coordinateKernels h).map (BinaryColumns.vectorFactor k)).prod := by
  change tensorColumns k (frame weightPhase).toLinearMap = _
  rw [← tensorColumns_kernel_prod, kernel_prod_eq_frame, coordinateKernels_phase]

end Columns
section ActualTerminals
open ComplexRank25 ComplexPhaseBudget ComplexFramedExecution

/-- The actual binary coordinate vector spanning one physical X terminal. -/
noncomputable def terminalVector (b : Wires.Address 25) : BinaryWalsh.Address (25 ^ 3) :=
  TensorCoordinates.coordinates 25 (Labels.cubeVector (K := ZMod 2) b.1.val b.2.1.val b.2.2.val)

theorem terminalVector_norm (b : Wires.Address 25) :
    Labels.binary (25 ^ 3) (terminalVector b) (terminalVector b) = 1 := by
  rw [terminalVector, TensorCoordinates.coordinates_isometry]
  exact Labels.binary_cube_self _ _ _ b.1.property b.2.1.property b.2.2.property

theorem terminalVector_weight (b : Wires.Address 25) : weight (terminalVector b) = 27 :=
  TensorTerminalWeight.weight_triples b.1 b.2.1 b.2.2

theorem terminal_phase_power (b : Wires.Address 25) (k : ℕ) :
    phase (weightPhase (terminalVector b)) ^ k = Complex.I ^ (27 * k) := by
  rw [weightPhase_eq_weight, terminalVector_weight, pow_mul]
  congr 1
  change Complex.I ^ 3 = Complex.I ^ 27
  norm_num [pow_succ, Complex.I_mul_I]

theorem coordinate_terminal (b : Wires.Address 25) :
    LabelTransport.label (TensorCoordinates.coordinates 25) (GlobalLabels.terminal (K := ZMod 2) vector b) =
      (ZMod 2) ∙ terminalVector b := by
  simp only [LabelTransport.label, GlobalLabels.terminal, Submodule.map_span, Set.image_singleton]
  rfl

private theorem label_top {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F) : LabelTransport.label e ⊤ = ⊤ := by
  rw [LabelTransport.label, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

private theorem label_orthogonal {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y) (U : Submodule K E) :
    LabelTransport.label e (B.orthogonal U) = C.orthogonal (LabelTransport.label e U) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [LabelTransport.mem_label, LabelTransport.mem_orthogonal B C e he]

theorem coordinate_complement (b : Wires.Address 25) :
    LabelTransport.label (TensorCoordinates.coordinates 25)
      ((GlobalProjectionRank.cubeForm (Labels.binary 25)).orthogonal (GlobalLabels.terminal (K := ZMod 2) vector b)) =
      (Labels.binary (25 ^ 3)).orthogonal ((ZMod 2) ∙ terminalVector b) := by
  change LabelTransport.label (TensorCoordinates.coordinates 25)
    ((Labels.cubeForm (Labels.binary 25)).orthogonal (GlobalLabels.terminal (K := ZMod 2) vector b)) = _
  rw [label_orthogonal _ _ _ (TensorCoordinates.coordinates_isometry 25), coordinate_terminal]

theorem frameOf_bot (k : ℕ) : frameOf k ⊥ = LinearEquiv.refl ℚ _ := by
  unfold frameOf BinaryColumnFrame.rationalLabelFrame
  rw [LabelTransport.label, Submodule.map_bot, labelFrame_bot]
  rfl

theorem frameOf_top (k : ℕ) : frameOf k ⊤ = (fullFrame k).restrictScalars ℚ := by
  unfold frameOf BinaryColumnFrame.rationalLabelFrame
  rw [label_top, labelFrame_top]

theorem frameOf_terminal (k : ℕ) (b : Wires.Address 25) :
    frameOf k (GlobalLabels.terminal (K := ZMod 2) vector b) =
      BinaryColumnFrame.rationalLabelFrame coordinateSymm k ((ZMod 2) ∙ terminalVector b) := by
  unfold frameOf
  rw [coordinate_terminal]

theorem frameOf_complement (k : ℕ) (b : Wires.Address 25) :
    frameOf k ((GlobalProjectionRank.cubeForm (Labels.binary 25)).orthogonal
      (GlobalLabels.terminal (K := ZMod 2) vector b)) =
      BinaryColumnFrame.rationalLabelFrame coordinateSymm k
        ((Labels.binary (25 ^ 3)).orthogonal ((ZMod 2) ∙ terminalVector b)) := by
  unfold frameOf
  rw [coordinate_complement]

/-- Physical source correction: the triple sign character is applied only
to X inputs, independently in each binary address column. -/
noncomputable def correctInput (k : ℕ) (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    Wire → BinaryColumns.Arrays (25 ^ 3) k
  | Sum.inl b => signColumns k (terminalVector b) (stored (Sum.inl b))
  | Sum.inr i => stored (Sum.inr i)

/-- Physical sink correction followed by undoing the signed bank exchange.
The scalar is applied once to the complete Y output array. -/
noncomputable def correctOutput (k : ℕ) (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    Wire → BinaryColumns.Arrays (25 ^ 3) k
  | Sum.inl b => Complex.I ^ (27 * k) • signColumns k (terminalVector b) (stored (Sum.inr (Sum.inl b)))
  | Sum.inr (Sum.inl b) => -stored (Sum.inl b)
  | Sum.inr (Sum.inr s) => stored (Sum.inr (Sum.inr s))

/-- The actual physical h=25 network, with the manuscript's explicit diagonal
source/sink corrections and signed rerouting, applies the full forward tensor
to every data and dirty-scratch input array. -/
theorem corrected_network_run (k : ℕ) (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    correctOutput k (FramedCircuit.run (network k) (correctInput k stored)) =
      fun i => fullFrame k (stored i) := by
  funext i
  rcases i with b | b | s
  · change Complex.I ^ (27 * k) • signColumns k (terminalVector b)
      (FramedCircuit.run (network k) (correctInput k stored) (Sum.inr (Sum.inl b))) = _
    rw [network_run]
    simp only [ComplexFramedExecution.sign, route, one_smul, GlobalLabels.sink, GlobalLabels.source, Sum.elim_inr,
      Sum.elim_inl, correctInput]
    change Complex.I ^ (27 * k) • signColumns k (terminalVector b)
      (frameOf k ((GlobalProjectionRank.cubeForm (Labels.binary 25)).orthogonal
        (GlobalLabels.terminal (K := ZMod 2) vector b))
        ((frameOf k (GlobalLabels.terminal (K := ZMod 2) vector b)).symm
          (signColumns k (terminalVector b) (stored (Sum.inl b))))) = _
    rw [frameOf_complement, frameOf_terminal, ← terminal_phase_power b k]
    exact corrected_column_endpoint coordinateSymm k (terminalVector b) (terminalVector_norm b) _
  · change -(FramedCircuit.run (network k) (correctInput k stored) (Sum.inl b)) = _
    rw [network_run]
    simp only [ComplexFramedExecution.sign, route, GlobalLabels.sink, GlobalLabels.source, Sum.elim_inl, Sum.elim_inr,
      correctInput, frameOf_bot, frameOf_top, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
      neg_one_smul, map_neg, neg_neg]
    rfl
  · change FramedCircuit.run (network k) (correctInput k stored) (Sum.inr (Sum.inr s)) = _
    rw [network_run]
    simp only [ComplexFramedExecution.sign, route, GlobalLabels.sink, GlobalLabels.source, Sum.elim_inr,
      correctInput, frameOf_bot, frameOf_top, LinearEquiv.refl_symm, LinearEquiv.refl_apply, one_smul]
    rfl

/-- The literal rank-factor instruction execution satisfies the same corrected
terminal transform, with every scalar gate and physical placement retained. -/
theorem corrected_lowered_run (k : ℕ) (directions : Directions) (hd : Realizes directions)
    (stored : Wire → BinaryColumns.Arrays (25 ^ 3) k) :
    correctOutput k (FramedFactorExecution.run (lowered k directions) (correctInput k stored)) =
      fun i => fullFrame k (stored i) := by
  rw [lowered, FramedFactorExecution.run_lower _ _ (factor_certificate k directions hd)]
  exact corrected_network_run k stored

/-- One finite direction family gives the explicitly corrected terminal
transform and the strict branching budget, uniformly in column count. -/
theorem exists_corrected_execution_budget :
    ∃ directions : Directions, Realizes directions ∧
      ∀ k, FramedFactorExecution.linearCount (lowered k directions) ≤ 916333630984500000 ∧
        (FramedFactorExecution.linearCount (lowered k directions) : ℝ) / 58645352620000 <
          (15625 : ℝ) ^ Parameters.sigma ∧
        ∀ stored : Wire → BinaryColumns.Arrays (25 ^ 3) k,
          correctOutput k (FramedFactorExecution.run (lowered k directions) (correctInput k stored)) =
            fun i => fullFrame k (stored i) := by
  obtain ⟨directions, hd, he⟩ := exists_uniform_execution_budget
  exact ⟨directions, hd, fun k => ⟨(he k).1, (he k).2.1, corrected_lowered_run k directions hd⟩⟩

end ActualTerminals
end IntegerMultBounds.Networks.ComplexEndpoints
