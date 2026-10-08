import IntegerMultBounds.Networks.TensorSubspace
import IntegerMultBounds.Networks.ProjectionRank

/-! The actual local tensor-label table for one motif invocation. The earlier
space splits as the orthogonal complement of a nondegenerate line plus that
line. Gate labels are embedded tensor subspaces, not dimension annotations.
The side-wire comparison uses orthogonality of its two physical triple lines.
Tensoring by the future line preserves every dimension and comparison. -/

namespace IntegerMultBounds.Networks.MotifLabels

open scoped TensorProduct
open Module TensorSubspace

section OrthogonalSums
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Orthogonal sums of actual nondegenerate subspaces remain nondegenerate. -/
theorem orthogonal_sup_nondegenerate (B : LinearMap.BilinForm K V) (hs : B.IsSymm)
    (U W : Submodule K V) (hu : (B.restrict U).Nondegenerate)
    (hw : (B.restrict W).Nondegenerate) (huw : U ≤ B.orthogonal W) :
    (B.restrict (U ⊔ W)).Nondegenerate := by
  have hl : (B.restrict (U ⊔ W)).SeparatingLeft := by
    rintro ⟨x, hx⟩ hxorth
    obtain ⟨u, huMem, w, hwMem, rfl⟩ := Submodule.mem_sup.mp hx
    have hu0 : (⟨u, huMem⟩ : U) = 0 := by
      apply hu.1
      intro y
      have hh := hxorth ⟨y, Submodule.mem_sup_left y.property⟩
      have hcross : B w y = 0 := huw y.property w hwMem
      change B (u + w) y = 0 at hh
      change B u y = 0
      simpa only [map_add, LinearMap.add_apply, hcross, add_zero] using hh
    have hw0 : (⟨w, hwMem⟩ : W) = 0 := by
      apply hw.1
      intro y
      have hh := hxorth ⟨y, Submodule.mem_sup_right y.property⟩
      have hcross : B u y = 0 := (hs.eq u y).trans (huw huMem y y.property)
      change B (u + w) y = 0 at hh
      change B w y = 0
      simpa only [map_add, LinearMap.add_apply, hcross, zero_add] using hh
    apply Subtype.ext
    have hu' : u = 0 := congrArg Subtype.val hu0
    have hw' : w = 0 := congrArg Subtype.val hw0
    simp [hu', hw']
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  exact (hs.eq x y).trans (hx y)

theorem top_nondegenerate (B : LinearMap.BilinForm K V) (hn : B.Nondegenerate) :
    (B.restrict ⊤).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact hn.1 x (fun y => hx ⟨y, Submodule.mem_top⟩)
  · intro x hx
    apply Subtype.ext
    exact hn.2 x (fun y => hx ⟨y, Submodule.mem_top⟩)

theorem bot_nondegenerate (B : LinearMap.BilinForm K V) :
    (B.restrict ⊥).Nondegenerate := by
  exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
/-- A subspace filling the whole ambient space with a nondegenerate label,
while orthogonal to that label, is its actual orthogonal complement. -/
theorem orthogonal_eq_of_sup [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hs : B.IsSymm) (U W : Submodule K V) (hu : (B.restrict U).Nondegenerate)
    (hW : W ≤ B.orthogonal U) (hfull : U ⊔ W = ⊤) : W = B.orthogonal U := by
  have hc := B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hu
  have hd := hc.disjoint.mono_right hW
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq U (B.orthogonal U)
  rw [hfull, hd.eq_bot, finrank_bot, add_zero] at h1
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_bot, add_zero] at h2
  exact Submodule.eq_of_le_of_finrank_le hW (by omega)

end OrthogonalSums

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

/-- Data defining the earlier orthogonal splitting and the current tensor factor.
No gate-label comparability or residual dimension is assumed. -/
structure Geometry (K E F : Type*) [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] where
  earlier : LinearMap.BilinForm K E
  current : LinearMap.BilinForm K F
  earlier_symm : earlier.IsSymm
  current_symm : current.IsSymm
  earlier_nd : earlier.Nondegenerate
  current_nd : current.Nondegenerate
  p : E
  p_norm : earlier p p ≠ 0

namespace Geometry
variable (g : Geometry K E F)

def past : Submodule K E := K ∙ g.p
def base : Submodule K E := g.earlier.orthogonal g.past
def pairing : LinearMap.BilinForm K (E ⊗[K] F) := form g.earlier g.current

def common : Submodule K (E ⊗[K] F) := space g.base ⊤
def full (_g : Geometry K E F) : Submodule K (E ⊗[K] F) := space (⊤ : Submodule K E) (⊤ : Submodule K F)
def xIn (_g : Geometry K E F) (t : F) : Submodule K (E ⊗[K] F) := space (⊤ : Submodule K E) (K ∙ t)
def yIn (t : F) : Submodule K (E ⊗[K] F) := space g.base (K ∙ t)
def xMiddle (t : F) : Submodule K (E ⊗[K] F) := g.common ⊔ space g.past (K ∙ t)
def yOut (t : F) : Submodule K (E ⊗[K] F) :=
  g.common ⊔ space g.past (g.current.orthogonal (K ∙ t))

/-- Times zero through seven of the manuscript table, suppressing future Q. -/
def gateLabel (r : Fin 8) (t : F) : Submodule K (E ⊗[K] F) :=
  if r = 0 then g.yIn t else if r = 1 then g.common else if r = 2 then g.xMiddle t
  else if r = 3 then g.full else if r = 4 then g.common else if r = 5 then g.yOut t
  else g.full

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem pairing_symm : g.pairing.IsSymm := by
  exact LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp g.earlier_symm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp g.current_symm))

theorem pairing_nondegenerate : g.pairing.Nondegenerate :=
  Labels.tmul_nondegenerate _ _ g.earlier_nd g.current_nd

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem past_nondegenerate : (g.earlier.restrict g.past).Nondegenerate :=
  Labels.line_nondegenerate g.earlier g.p g.p_norm

omit [FiniteDimensional K F] in
theorem base_nondegenerate : (g.earlier.restrict g.base).Nondegenerate :=
  ProjectionRank.orthogonal_nondegenerate _ g.earlier_symm g.earlier_nd _ g.past_nondegenerate

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem base_sup_past : g.base ⊔ g.past = ⊤ :=
  (LinearMap.BilinForm.isCompl_span_singleton_orthogonal g.p_norm).symm.sup_eq_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem past_finrank : finrank K g.past = 1 := by
  apply finrank_span_singleton
  intro hp
  exact g.p_norm (by simp [hp])

omit [FiniteDimensional K F] in
theorem base_finrank_add : finrank K g.base + 1 = finrank K E := by
  have hi : IsCompl g.past g.base := LinearMap.BilinForm.isCompl_span_singleton_orthogonal g.p_norm
  have hd := Submodule.finrank_sup_add_finrank_inf_eq g.base g.past
  rw [g.base_sup_past, hi.symm.inf_eq_bot, finrank_bot, add_zero, g.past_finrank] at hd
  simpa using hd.symm

theorem common_nondegenerate : (g.pairing.restrict g.common).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ g.base_nondegenerate (top_nondegenerate _ g.current_nd)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem full_eq_top : g.full = ⊤ := top_top

theorem full_nondegenerate : (g.pairing.restrict g.full).Nondegenerate := by
  rw [g.full_eq_top]
  exact top_nondegenerate _ g.pairing_nondegenerate

theorem xIn_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.xIn t)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ (top_nondegenerate _ g.earlier_nd)
    (Labels.line_nondegenerate _ _ ht)

theorem yIn_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.yIn t)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ g.base_nondegenerate (Labels.line_nondegenerate _ _ ht)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_orthogonal_past (U : Submodule K F) :
    g.common ≤ g.pairing.orthogonal (space g.past U) :=
  orthogonal_left _ _ _ _ le_rfl

theorem xMiddle_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.xMiddle t)).Nondegenerate :=
  orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate (Labels.line_nondegenerate _ _ ht))
    (g.common_orthogonal_past _)

theorem yOut_nondegenerate (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.yOut t)).Nondegenerate :=
  orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate
      (ProjectionRank.orthogonal_nondegenerate _ g.current_symm g.current_nd _
        (Labels.line_nondegenerate _ _ ht))) (g.common_orthogonal_past _)

/-- Nondegeneracy is proved for each of the eight actual labels. -/
theorem gateLabel_nondegenerate (r : Fin 8) (t : F) (ht : g.current t t ≠ 0) :
    (g.pairing.restrict (g.gateLabel r t)).Nondegenerate := by
  fin_cases r <;> simp only [gateLabel, Fin.isValue]
  all_goals first | exact g.yIn_nondegenerate t ht | exact g.common_nondegenerate |
    exact g.xMiddle_nondegenerate t ht | exact g.full_nondegenerate | exact g.yOut_nondegenerate t ht

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- The earlier decomposition yields the prescribed incoming X label. -/
theorem xIn_le_middle (t : F) : g.xIn t ≤ g.xMiddle t := by
  change space ⊤ (K ∙ t) ≤ g.common ⊔ space g.past (K ∙ t)
  rw [← g.base_sup_past, sup_left]
  exact sup_le_sup (mono le_rfl le_top) le_rfl

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem yIn_le_common (t : F) : g.yIn t ≤ g.common := mono le_rfl le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_le_yOut (t : F) : g.common ≤ g.yOut t := le_sup_left

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem middle_le_full (t : F) : g.xMiddle t ≤ g.full := by rw [g.full_eq_top]; exact le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem yOut_le_full (t : F) : g.yOut t ≤ g.full := by rw [g.full_eq_top]; exact le_top

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem common_le_full : g.common ≤ g.full := mono le_top le_rfl

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- This is the essential neighbor-dependent comparison on a side wire. -/
theorem neighbor_line (tX tY : F) (hneigh : g.current tX tY = 0) :
    K ∙ tX ≤ g.current.orthogonal (K ∙ tY) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hyx : g.current tY tX = 0 := (g.current_symm.eq tY tX).trans hneigh
  simp [map_smul, LinearMap.smul_apply, hyx]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem side_middle_le_out (tX tY : F) (hneigh : g.current tX tY = 0) :
    g.xMiddle tX ≤ g.yOut tY :=
  sup_le_sup le_rfl (mono le_rfl (g.neighbor_line tX tY hneigh))

/-- The side-wire last label is exactly the complement of the exposed tensor
line, which is the earlier-space complement needed by the next stage. -/
theorem yOut_eq_orthogonal (t : F) (ht : g.current t t ≠ 0) :
    g.yOut t = g.pairing.orthogonal (space g.past (K ∙ t)) := by
  apply orthogonal_eq_of_sup _ g.pairing_symm
    (space g.past (K ∙ t)) (g.yOut t)
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate
      (Labels.line_nondegenerate _ _ ht))
  · exact sup_le (g.common_orthogonal_past _)
      (orthogonal_right g.earlier g.current g.past g.past le_rfl)
  · have hcurrent : (K ∙ t) ⊔ g.current.orthogonal (K ∙ t) = ⊤ :=
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal ht).sup_eq_top
    have hsplit : space g.past (K ∙ t) ⊔ space g.past (g.current.orthogonal (K ∙ t)) =
        space g.past (⊤ : Submodule K F) := by rw [← sup_right, hcurrent]
    have hfull : g.common ⊔ space g.past (⊤ : Submodule K F) = ⊤ := by
      change space g.base ⊤ ⊔ space g.past ⊤ = ⊤
      rw [← sup_left, g.base_sup_past, top_top]
    calc
      space g.past (K ∙ t) ⊔ g.yOut t =
          g.common ⊔ (space g.past (K ∙ t) ⊔
            space g.past (g.current.orthogonal (K ∙ t))) := by dsimp [yOut]; ac_rfl
      _ = ⊤ := by rw [hsplit, hfull]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Every X data edge in the local table is increasing or stationary. -/
theorem x_chain (t : F) :
    List.IsChain (· ≤ ·) [g.xIn t, g.xMiddle t, g.full, g.full, g.full] := by
  simp [List.isChain_cons_cons, g.xIn_le_middle, g.middle_le_full]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Every Y data edge in the local table is increasing or stationary. -/
theorem y_chain (t : F) :
    List.IsChain (· ≤ ·) [g.yIn t, g.yIn t, g.common, g.common, g.yOut t] := by
  simp [List.isChain_cons_cons, g.yIn_le_common, g.common_le_yOut]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Side scratch grows from zero along its actual neighboring-pair path. -/
theorem side_chain (tX tY : F) (hneigh : g.current tX tY = 0) :
    List.IsChain (· ≤ ·) [⊥, g.yIn tY, g.xMiddle tX, g.yOut tY, g.full] := by
  have h02 : g.yIn tY ≤ g.xMiddle tX := (g.yIn_le_common tY).trans le_sup_left
  simp [List.isChain_cons_cons, h02, g.side_middle_le_out tX tY hneigh, g.yOut_le_full]

/-- The unique returning central edge removes the entire remaining tensor factor. -/
theorem central_dimension_loss : finrank K g.full - finrank K g.common = finrank K F := by
  have hb := g.base_finrank_add
  change finrank K (space (⊤ : Submodule K E) (⊤ : Submodule K F)) -
    finrank K (space g.base (⊤ : Submodule K F)) = finrank K F
  rw [finrank_space, finrank_space]
  have ht : finrank K (⊤ : Submodule K E) = finrank K E := by simp
  have hf : finrank K (⊤ : Submodule K F) = finrank K F := by simp
  rw [ht, hf]
  have he := congrArg (· * finrank K F) hb
  simp only [Nat.add_mul, one_mul] at he
  omega

/-- The rank loss is also the dimension of the actual orthogonal residual. -/
theorem central_residual_dimension :
    finrank K (ProjectionRank.residual g.pairing g.common g.full) = finrank K F := by
  rw [ProjectionRank.residual_finrank _ g.pairing_symm _ _ g.common_nondegenerate
    g.common_le_full, g.central_dimension_loss]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Central scratch visits 0, common, full, common, full. All edges except the
middle return increase; the comparison at that return is reversed. -/
theorem central_edges :
    (⊥ : Submodule K (E ⊗[K] F)) ≤ g.common ∧
      g.common ≤ g.full ∧ g.common ≤ g.full ∧ g.common ≤ g.full :=
  ⟨bot_le, g.common_le_full, g.common_le_full, g.common_le_full⟩

/-- The removed central subspace is concretely P tensor F. -/
theorem central_residual_eq :
    ProjectionRank.residual g.pairing g.common g.full =
      space g.past (⊤ : Submodule K F) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply le_inf
    · rw [g.full_eq_top]
      exact le_top
    · intro x hx y hy
      exact (g.pairing_symm.eq y x).trans (g.common_orthogonal_past ⊤ hy x hx)
  · rw [g.central_residual_dimension, finrank_space, g.past_finrank, one_mul]
    simp

/-- Central vertices in chronological order: source, time1, time3, time4, time6. -/
def centralLabel (i : Fin 5) : Submodule K (E ⊗[K] F) :=
  if i = 0 then ⊥ else if i = 1 then g.common else if i = 2 then g.full
  else if i = 3 then g.common else g.full

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Only the time3-to-time4 edge has reversed inclusion. -/
theorem central_comparable (i : Fin 4) :
    if i = 2 then g.centralLabel i.succ ≤ g.centralLabel i.castSucc
    else g.centralLabel i.castSucc ≤ g.centralLabel i.succ := by
  fin_cases i <;> simp [centralLabel, g.common_le_full]

/-- If F has positive dimension, the central return is the unique strict
decrease in the listed central trajectory. The other wire paths are chains. -/
theorem central_strict_decrease_iff (hF : 0 < finrank K F) (i : Fin 4) :
    g.centralLabel i.succ < g.centralLabel i.castSucc ↔ i = 2 := by
  have hstrict : g.common < g.full := lt_of_le_of_ne g.common_le_full (by
    intro he
    have hd := g.central_dimension_loss
    rw [he, Nat.sub_self] at hd
    omega)
  fin_cases i <;> simp [centralLabel, hstrict, not_lt_of_ge g.common_le_full]

section Future
variable {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- Restore the one-dimensional future factor in the actual ambient tensor space. -/
def liftLabel (q : H) (U : Submodule K (E ⊗[K] F)) :
    Submodule K ((E ⊗[K] F) ⊗[K] H) := space U (K ∙ q)

def liftedPairing (D : LinearMap.BilinForm K H) :
    LinearMap.BilinForm K ((E ⊗[K] F) ⊗[K] H) := form g.pairing D

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
theorem liftLabel_mono (q : H) {U V : Submodule K (E ⊗[K] F)} (hUV : U ≤ V) :
    liftLabel q U ≤ liftLabel q V := mono hUV le_rfl

theorem liftLabel_finrank (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (U : Submodule K (E ⊗[K] F)) : finrank K (liftLabel q U) = finrank K U := by
  change finrank K (space U (K ∙ q)) = _
  rw [finrank_space, finrank_span_singleton (show q ≠ 0 from fun hz => hq (by simp [hz])), mul_one]

theorem liftLabel_nondegenerate (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (U : Submodule K (E ⊗[K] F)) (hU : (g.pairing.restrict U).Nondegenerate) :
    ((g.liftedPairing D).restrict (liftLabel q U)).Nondegenerate :=
  TensorSubspace.nondegenerate _ _ _ _ hU (Labels.line_nondegenerate _ _ hq)

/-- All table entries stay nondegenerate after restoring Q, with no increase
in their dimensions because Q is an actual nondegenerate line. -/
theorem lifted_gateLabel (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (r : Fin 8) (t : F) (ht : g.current t t ≠ 0) :
    ((g.liftedPairing D).restrict (liftLabel q (g.gateLabel r t))).Nondegenerate ∧
      finrank K (liftLabel q (g.gateLabel r t)) = finrank K (g.gateLabel r t) :=
  ⟨g.liftLabel_nondegenerate D q hq _ (g.gateLabel_nondegenerate r t ht),
    liftLabel_finrank D q hq _⟩

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
theorem lifted_x_chain (q : H) (t : F) :
    List.IsChain (· ≤ ·)
      ([g.xIn t, g.xMiddle t, g.full, g.full, g.full].map (liftLabel q)) := by
  rw [List.isChain_map]
  exact (g.x_chain t).imp (fun {_ _} h => liftLabel_mono q h)

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
theorem lifted_y_chain (q : H) (t : F) :
    List.IsChain (· ≤ ·)
      ([g.yIn t, g.yIn t, g.common, g.common, g.yOut t].map (liftLabel q)) := by
  rw [List.isChain_map]
  exact (g.y_chain t).imp (fun {_ _} h => liftLabel_mono q h)

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
/-- Including its zero source and full ambient sink, the side wire never decreases. -/
theorem lifted_side_chain (q : H) (tX tY : F) (hneigh : g.current tX tY = 0) :
    List.IsChain (· ≤ ·) [⊥, liftLabel q (g.yIn tY), liftLabel q (g.xMiddle tX),
      liftLabel q (g.yOut tY), liftLabel q g.full, ⊤] := by
  have h02 := liftLabel_mono q ((g.yIn_le_common tY).trans
    (show g.common ≤ g.xMiddle tX from le_sup_left))
  have h25 := liftLabel_mono q (g.side_middle_le_out tX tY hneigh)
  have h57 := liftLabel_mono q (g.yOut_le_full tY)
  simp [List.isChain_cons_cons, h02, h25, h57]

theorem lifted_central_dimension_loss (D : LinearMap.BilinForm K H) (q : H)
    (hq : D q q ≠ 0) :
    finrank K (liftLabel q g.full) - finrank K (liftLabel q g.common) = finrank K F := by
  rw [liftLabel_finrank D q hq, liftLabel_finrank D q hq, g.central_dimension_loss]

theorem lifted_central_residual_dimension (D : LinearMap.BilinForm K H) (hs : D.IsSymm)
    (q : H) (hq : D q q ≠ 0) :
    finrank K (ProjectionRank.residual (g.liftedPairing D)
      (liftLabel q g.common) (liftLabel q g.full)) = finrank K F := by
  have hsym : (g.liftedPairing D).IsSymm := LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp g.pairing_symm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp hs))
  rw [ProjectionRank.residual_finrank _ hsym _ _
    (g.liftLabel_nondegenerate D q hq _ g.common_nondegenerate)
    (liftLabel_mono q g.common_le_full), g.lifted_central_dimension_loss D q hq]

/-- The exact decrease after tensoring by Q remains P tensor F tensor Q. -/
theorem lifted_central_residual_eq (D : LinearMap.BilinForm K H) (hs : D.IsSymm)
    (q : H) (hq : D q q ≠ 0) :
    ProjectionRank.residual (g.liftedPairing D) (liftLabel q g.common) (liftLabel q g.full) =
      liftLabel q (space g.past (⊤ : Submodule K F)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply le_inf
    · apply liftLabel_mono
      rw [g.full_eq_top]
      exact le_top
    · apply orthogonal_left g.pairing D (K ∙ q) (K ∙ q)
      intro x hx y hy
      exact (g.pairing_symm.eq y x).trans (g.common_orthogonal_past ⊤ hy x hx)
  · rw [g.lifted_central_residual_dimension D hs q hq,
      liftLabel_finrank D q hq, finrank_space, g.past_finrank, one_mul]
    simp

/-- The complete physical central-wire path includes its zero source and
whole-ambient sink, in addition to times 1,3,4,6. -/
def futureCentralLabel (q : H) (i : Fin 6) : Submodule K ((E ⊗[K] F) ⊗[K] H) :=
  if i = 0 then ⊥ else if i = 1 then liftLabel q g.common
  else if i = 2 then liftLabel q g.full else if i = 3 then liftLabel q g.common
  else if i = 4 then liftLabel q g.full else ⊤

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H] in
theorem futureCentral_comparable (q : H) (i : Fin 5) :
    if i = 2 then g.futureCentralLabel q i.succ ≤ g.futureCentralLabel q i.castSucc
    else g.futureCentralLabel q i.castSucc ≤ g.futureCentralLabel q i.succ := by
  have hm := liftLabel_mono q g.common_le_full
  fin_cases i <;> simp [futureCentralLabel, hm]

/-- Restoring Q and both scratch endpoints introduces no additional decrease. -/
theorem futureCentral_strict_decrease_iff (D : LinearMap.BilinForm K H)
    (q : H) (hq : D q q ≠ 0) (hF : 0 < finrank K F) (i : Fin 5) :
    g.futureCentralLabel q i.succ < g.futureCentralLabel q i.castSucc ↔ i = 2 := by
  have hm := liftLabel_mono q g.common_le_full
  have hstrict : liftLabel q g.common < liftLabel q g.full := lt_of_le_of_ne hm (by
    intro he
    have hd := g.lifted_central_dimension_loss D q hq
    rw [he, Nat.sub_self] at hd
    omega)
  fin_cases i <;> simp [futureCentralLabel, hstrict, not_lt_of_ge hm]

theorem futureCentral_nondegenerate (D : LinearMap.BilinForm K H)
    (hn : D.Nondegenerate) (q : H) (hq : D q q ≠ 0) (i : Fin 6) :
    ((g.liftedPairing D).restrict (g.futureCentralLabel q i)).Nondegenerate := by
  fin_cases i <;> simp only [futureCentralLabel, Fin.isValue]
  all_goals first
    | exact bot_nondegenerate _
    | exact g.liftLabel_nondegenerate D q hq _ g.common_nondegenerate
    | exact g.liftLabel_nondegenerate D q hq _ g.full_nondegenerate
    | exact top_nondegenerate _ (Labels.tmul_nondegenerate _ _ g.pairing_nondegenerate hn)

/-- Scratch's final enlargement to the whole ambient tensor space is comparable
and nondegenerate whenever the three ambient factor forms are nondegenerate. -/
theorem scratch_sink (D : LinearMap.BilinForm K H) (hn : D.Nondegenerate)
    (q : H) (hq : D q q ≠ 0) :
    liftLabel q g.full ≤ ⊤ ∧
      ((g.liftedPairing D).restrict (liftLabel q g.full)).Nondegenerate ∧
      ((g.liftedPairing D).restrict ⊤).Nondegenerate :=
  ⟨le_top, g.liftLabel_nondegenerate D q hq _ g.full_nondegenerate,
    top_nondegenerate _ (Labels.tmul_nondegenerate _ _ g.pairing_nondegenerate hn)⟩
end Future

end Geometry
end IntegerMultBounds.Networks.MotifLabels
