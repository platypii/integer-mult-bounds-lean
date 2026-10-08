import IntegerMultBounds.Networks.BinaryRankFactors

/-! Genuine invertible frames on arrays with any number of binary columns.
Their forward and inverse maps are the actual column operators. Restricting
scalars exposes the same complex-array maps to rational module compilers;
this changes neither the arrays nor the operators and asserts no runtime. -/

namespace IntegerMultBounds.Networks.BinaryColumnFrame

open BinaryColumns

variable {h k : ℕ}

/-- Lift a one-column linear equivalence to all columns, with its concrete
columnwise inverse. This includes the zero-column identity operator. -/
noncomputable def tensorEquiv (k : ℕ)
    (T : BinaryWalsh.Arrays h ≃ₗ[ℂ] BinaryWalsh.Arrays h) :
    Arrays h k ≃ₗ[ℂ] Arrays h k :=
  { tensorColumns k T.toLinearMap with
    invFun := tensorColumns k T.symm.toLinearMap
    left_inv := by
      intro f
      change (tensorColumns k T.symm.toLinearMap * tensorColumns k T.toLinearMap) f = f
      rw [← tensorColumns_mul]
      have hi : T.symm.toLinearMap * T.toLinearMap = 1 := by
        apply LinearMap.ext
        intro x
        exact T.symm_apply_apply x
      rw [hi, tensorColumns_one]
      rfl
    right_inv := by
      intro f
      change (tensorColumns k T.toLinearMap * tensorColumns k T.symm.toLinearMap) f = f
      rw [← tensorColumns_mul]
      have hi : T.toLinearMap * T.symm.toLinearMap = 1 := by
        apply LinearMap.ext
        intro x
        exact T.apply_symm_apply x
      rw [hi, tensorColumns_one]
      rfl }

@[simp] theorem tensorEquiv_toLinearMap (k : ℕ)
    (T : BinaryWalsh.Arrays h ≃ₗ[ℂ] BinaryWalsh.Arrays h) :
    (tensorEquiv k T).toLinearMap = tensorColumns k T.toLinearMap := rfl

@[simp] theorem tensorEquiv_symm_toLinearMap (k : ℕ)
    (T : BinaryWalsh.Arrays h ≃ₗ[ℂ] BinaryWalsh.Arrays h) :
    (tensorEquiv k T).symm.toLinearMap = tensorColumns k T.symm.toLinearMap := rfl

/-- The actual whole-array Walsh/phase frame for a binary address phase. -/
noncomputable def frameEquiv (k : ℕ) (q : BinaryWalsh.Address h → ZMod 4) :
    Arrays h k ≃ₗ[ℂ] Arrays h k := tensorEquiv k (BinaryWalsh.frame q)

@[simp] theorem frameEquiv_toLinearMap (k : ℕ) (q : BinaryWalsh.Address h → ZMod 4) :
    (frameEquiv k q).toLinearMap = tensorColumns k (BinaryWalsh.frame q).toLinearMap := rfl

@[simp] theorem frameEquiv_symm_toLinearMap (k : ℕ) (q : BinaryWalsh.Address h → ZMod 4) :
    (frameEquiv k q).symm.toLinearMap = tensorColumns k (BinaryWalsh.frame q).symm.toLinearMap := rfl

/-- A coordinate submodule labels its genuine projector-induced frame.
As for `ProjectionTrace.projector`, degenerate labels use its total fallback. -/
noncomputable def labelFrame (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) : Arrays h k ≃ₗ[ℂ] Arrays h k :=
  frameEquiv k (fun x => BinaryPhase.weightPhase (ProjectionTrace.projector (Labels.binary h) hs U x))

/-- The invertible frame edge is exactly the operator whose rank factorization
was proved, with the same endpoints and inverse orientation. -/
theorem labelFrame_edge (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h)) :
    (labelFrame hs k V).toLinearMap * (labelFrame hs k U).symm.toLinearMap =
      BinaryRankFactors.edgeOperator hs k U V := rfl

theorem labelFrame_edge_apply (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h)) (f : Arrays h k) :
    labelFrame hs k V ((labelFrame hs k U).symm f) = BinaryRankFactors.edgeOperator hs k U V f := rfl

/-- Rational-linear access to the same complex-array frame for module compilers. -/
noncomputable def rationalLabelFrame (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) : Arrays h k ≃ₗ[ℚ] Arrays h k :=
  (labelFrame hs k U).restrictScalars ℚ

@[simp] theorem rationalLabelFrame_apply (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) (f : Arrays h k) :
    rationalLabelFrame hs k U f = labelFrame hs k U f := rfl

@[simp] theorem rationalLabelFrame_symm_apply (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) (f : Arrays h k) :
    (rationalLabelFrame hs k U).symm f = (labelFrame hs k U).symm f := rfl

/-- Scalar restriction preserves the precise edge operator, not only its rank. -/
theorem rationalLabelFrame_edge (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U V : Submodule (ZMod 2) (BinaryWalsh.Address h)) :
    (rationalLabelFrame hs k V).toLinearMap * (rationalLabelFrame hs k U).symm.toLinearMap =
      (BinaryRankFactors.edgeOperator hs k U V).restrictScalars ℚ := rfl

end IntegerMultBounds.Networks.BinaryColumnFrame
