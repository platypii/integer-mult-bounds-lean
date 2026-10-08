import IntegerMultBounds.Networks.GlobalLabels

/-! Nondegeneracy of the concrete physical global labels. -/

namespace IntegerMultBounds.Networks.GlobalLabels

open scoped TensorProduct
open GroupedCircuit GroupedFrames MotifLabels StageLabels

variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R]
  {n a c : ℕ}
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

include ht in
omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] in
/-- Future lift and the empty-prefix isometry preserve actual nondegeneracy. -/
theorem firstLabel_nondegenerate (q : B × B) (U : Submodule K (K ⊗[K] F))
    (hU : ((TensorSubspace.form unitForm D).restrict U).Nondegenerate) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict (firstLabel t q U)).Nondegenerate := by
  unfold firstLabel Geometry.liftLabel
  apply LabelTransport.nondegenerate
    (TensorSubspace.form (TensorSubspace.form (unitForm : LinearMap.BilinForm K K) D)
      (TensorSubspace.form D D)) _
    (firstEquiv (K := K) (F := F)) (first_pairing D)
  apply TensorSubspace.nondegenerate _ _ _ _ hU
  apply Labels.line_nondegenerate
  simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using mul_ne_zero (ht q.2) (ht q.1)

include ht in
omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] in
theorem secondLabel_nondegenerate (q : B × B) (U : Submodule K (F ⊗[K] F))
    (hU : ((TensorSubspace.form D D).restrict U).Nondegenerate) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict (secondLabel t q U)).Nondegenerate :=
  LabelTransport.nondegenerate
    (TensorSubspace.form (TensorSubspace.form D D) D)
    (TensorSubspace.form D (TensorSubspace.form D D))
    (secondEquiv (K := K) (F := F)) (second_pairing D) _
    (TensorSubspace.nondegenerate (TensorSubspace.form D D) D U (K ∙ t q.2) hU
      (Labels.line_nondegenerate D (t q.2) (ht q.2)))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] in
theorem thirdLabel_nondegenerate (q : B × B) (U : Submodule K ((F ⊗[K] F) ⊗[K] F))
    (hU : ((TensorSubspace.form (TensorSubspace.form D D) D).restrict U).Nondegenerate) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict
      (thirdLabel (K := K) (F := F) q U)).Nondegenerate :=
  LabelTransport.nondegenerate
    (TensorSubspace.form (TensorSubspace.form (TensorSubspace.form D D) D) unitForm)
    (TensorSubspace.form D (TensorSubspace.form D D))
    (thirdEquiv (K := K) (F := F)) (third_pairing D) _
    (TensorSubspace.nondegenerate (TensorSubspace.form (TensorSubspace.form D D) D)
      unitForm U (K ∙ (1 : K)) hU (Labels.line_nondegenerate (unitForm : LinearMap.BilinForm K K) (1 : K) (by simp [unitForm])))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Every group of the actual physical invocation carries a proved
nondegenerate cube subspace. -/
theorem invocation_nondegenerate (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B)
    (v : Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R)
    (hv : v ∈ invocation D hs hn t ht eB eA eC owner G J H j q) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
  unfold invocation at hv
  split_ifs at hv with hj0 hj1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact firstLabel_nondegenerate D t ht q w.label
      (LabeledMotif.forward_nondegenerate (firstGeometry D hs hn) (t ∘ eB) owner G J H
        (fun i => ht (eB i)) w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact secondLabel_nondegenerate D t ht q w.label
      (LabeledMotif.opposite_nondegenerate (secondGeometry D hs hn (t q.1) (ht q.1))
        (t ∘ eB) owner G J H (fun i => ht (eB i)) w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact thirdLabel_nondegenerate D q w.label
      (LabeledMotif.forward_nondegenerate
        (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) owner G J H (fun i => ht (eB i)) w hw)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem program_nondegenerate (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (v : Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R)
    (hv : v ∈ program D hs hn t ht eB eA eC owner G J H) :
    ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
  have hstage (j : Fin 3) (hv : v ∈ stage D hs hn t ht eB eA eC owner G J H j) :
      ((TensorSubspace.form D (TensorSubspace.form D D)).restrict v.label).Nondegenerate := by
    obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hv
    exact invocation_nondegenerate D hs hn t ht eB eA eC owner G J H j q v hq
  simp only [program, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · exact hstage 0 hv
  · exact hstage 1 hv
  · exact hstage 2 hv

end IntegerMultBounds.Networks.GlobalLabels
