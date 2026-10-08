import IntegerMultBounds.Networks.GlobalGrouped
import IntegerMultBounds.Networks.LabeledMotif
import IntegerMultBounds.Networks.StageLabels
import IntegerMultBounds.Networks.LabelTransport

/-! Actual tensor labels on the physical three-stage grouped schedule. Labels
are lifted by the future line, transported to a common cube, and attached to
exactly the existing global groups and invocation embeddings. -/

namespace IntegerMultBounds.Networks.GlobalLabels

open scoped TensorProduct
open GroupedCircuit GroupedFrames MotifLabels StageLabels

section Placement
variable {ι κ L M R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R] [DecidableEq R]

/-- Physical placement and label transport are performed together. -/
def place (f : ι ↪ κ) (labelMap : L → M) (v : Vertex ι L R) : Vertex κ M R :=
  ⟨GlobalGrouped.embedGroup f v.group, labelMap v.label⟩

def placeList (f : ι ↪ κ) (labelMap : L → M) (vs : List (Vertex ι L R)) :
    List (Vertex κ M R) := vs.map (place f labelMap)

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq R] in
theorem placeList_groups (f : ι ↪ κ) (labelMap : L → M) (vs : List (Vertex ι L R)) :
    (placeList f labelMap vs).map Vertex.group =
      GlobalGrouped.embedGroups f (vs.map Vertex.group) := by
  simp only [placeList, GlobalGrouped.embedGroups, List.map_map]
  rfl

/-- Placing a group neither adds nor loses a local physical incidence. -/
theorem touched_place (f : ι ↪ κ) (labelMap : L → M) (v : Vertex ι L R) (i : ι) :
    f i ∈ touched (place f labelMap v).group ↔ i ∈ touched v.group := by
  change f i ∈ touched (GlobalGrouped.embedGroup f v.group) ↔ _
  rw [← mem_support, GlobalGrouped.support_embed]
  simp only [Finset.mem_image, f.injective.eq_iff, exists_eq_right, mem_support]

theorem history_place (f : ι ↪ κ) (labelMap : L → M) (vs : List (Vertex ι L R)) (i : ι) :
    LabeledMotif.history (placeList f labelMap vs) (f i) =
      (LabeledMotif.history vs i).map labelMap := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [placeList, List.map_cons, LabeledMotif.history_cons] at *
    simp only [touched_place, ih, List.map_append]
    split_ifs <;> simp [place]
end Placement

section Schedule
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R]
  {n a c : ℕ}

variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

/-- Stage-one labels eliminate the empty earlier scalar factor. -/
def firstLabel (q : B × B) (U : Submodule K (K ⊗[K] F)) : Submodule K (Ambient K F) :=
  (Geometry.liftLabel (t q.1 ⊗ₜ[K] t q.2) U).map firstEquiv.toLinearMap

/-- Stage-two labels use the actual tensor associator. -/
def secondLabel (q : B × B) (U : Submodule K (F ⊗[K] F)) : Submodule K (Ambient K F) :=
  (Geometry.liftLabel (t q.2) U).map secondEquiv.toLinearMap

/-- Stage-three labels eliminate the empty future scalar factor. -/
def thirdLabel (_q : B × B) (U : Submodule K ((F ⊗[K] F) ⊗[K] F)) : Submodule K (Ambient K F) :=
  (Geometry.liftLabel (1 : K) U).map thirdEquiv.toLinearMap

/-- Each actual coordinate invocation carries the appropriate stage geometry;
the middle stage keeps the opposite inverse group's physical bank orientation. -/
def invocation (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  if j = 0 then
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (firstLabel t q)
      (LabeledMotif.forward (firstGeometry D hs hn) (t ∘ eB) owner G J H)
  else if j = 1 then
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (secondLabel t q)
      (LabeledMotif.opposite (secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H)
  else
    placeList (GlobalCircuit.localEmbedding eB eA eC j q) (thirdLabel (K := K) (F := F) q)
      (LabeledMotif.forward (thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2))
        (t ∘ eB) owner G J H)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Forgetting labels returns precisely the pre-existing physical invocation. -/
theorem invocation_groups (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) (q : B × B) :
    (invocation D hs hn t ht eB eA eC owner G J H j q).map Vertex.group =
      GlobalGrouped.invocationGroups eB eA eC owner G J H j q := by
  fin_cases j <;>
    simp [invocation, GlobalGrouped.invocationGroups, GlobalGrouped.localGroups,
      placeList_groups, LabeledMotif.forward_groups, LabeledMotif.opposite_groups]

def stage (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  (GlobalCircuit.keys eB).flatMap (invocation D hs hn t ht eB eA eC owner G J H j)

def program (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Vertex (GlobalCircuit.World B A C) (Submodule K (Ambient K F)) R) :=
  stage D hs hn t ht eB eA eC owner G J H 0 ++
    stage D hs hn t ht eB eA eC owner G J H 1 ++
    stage D hs hn t ht eB eA eC owner G J H 2

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem stage_groups (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) (j : Fin 3) :
    (stage D hs hn t ht eB eA eC owner G J H j).map Vertex.group =
      GlobalGrouped.stage eB eA eC owner G J H j := by
  simp only [stage, List.map_flatMap, invocation_groups, GlobalGrouped.stage, GlobalGrouped.partialStage]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- The complete labeled vertex list erases to the exact grouped network. -/
theorem program_groups (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
    (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
    (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    (program D hs hn t ht eB eA eC owner G J H).map Vertex.group =
      GlobalGrouped.program eB eA eC owner G J H := by
  simp only [program, List.map_append, stage_groups, GlobalGrouped.program]
end Schedule

section Endpoints
variable {K F B A C : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

/-- The terminal line at a physical three-coordinate data address. -/
def terminal (b : GlobalCircuit.Address B) : Submodule K (Ambient K F) :=
  K ∙ (t b.1 ⊗ₜ[K] (t b.2.1 ⊗ₜ[K] t b.2.2))

/-- Physical source labels: X carries its terminal line and every other bank
starts at zero. -/
def source : GlobalCircuit.World B A C → Submodule K (Ambient K F) :=
  Sum.elim (terminal t) (Sum.elim (fun _ => ⊥) (fun _ => ⊥))

/-- Physical sinks: X and scratch carry the whole ambient cube, while Y carries
the actual orthogonal complement of its terminal line. -/
def sink : GlobalCircuit.World B A C → Submodule K (Ambient K F) :=
  Sum.elim (fun _ => ⊤)
    (Sum.elim (fun b => (TensorSubspace.form D (TensorSubspace.form D D)).orthogonal (terminal t b))
      (fun _ => ⊤))

def xInput (j : Fin 3) (b : GlobalCircuit.Address B) : Submodule K (Ambient K F) :=
  if j = 0 then firstLabel t (b.2.1, b.2.2) ((firstGeometry D hs hn).xIn (t b.1))
  else if j = 1 then secondLabel t (b.1, b.2.2)
    ((secondGeometry D hs hn (t b.1) (ht b.1)).xIn (t b.2.1))
  else thirdLabel (K := K) (F := F) (b.1, b.2.1)
    ((thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).xIn (t b.2.2))

def yInput (j : Fin 3) (b : GlobalCircuit.Address B) : Submodule K (Ambient K F) :=
  if j = 0 then firstLabel t (b.2.1, b.2.2) ((firstGeometry D hs hn).yIn (t b.1))
  else if j = 1 then secondLabel t (b.1, b.2.2)
    ((secondGeometry D hs hn (t b.1) (ht b.1)).yIn (t b.2.1))
  else thirdLabel (K := K) (F := F) (b.1, b.2.1)
    ((thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).yIn (t b.2.2))

def xOutput (j : Fin 3) (b : GlobalCircuit.Address B) : Submodule K (Ambient K F) :=
  if j = 0 then firstLabel t (b.2.1, b.2.2) (firstGeometry D hs hn).full
  else if j = 1 then secondLabel t (b.1, b.2.2)
    (secondGeometry D hs hn (t b.1) (ht b.1)).full
  else thirdLabel (K := K) (F := F) (b.1, b.2.1)
    (thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).full

def yOutput (j : Fin 3) (b : GlobalCircuit.Address B) : Submodule K (Ambient K F) :=
  if j = 0 then firstLabel t (b.2.1, b.2.2) ((firstGeometry D hs hn).yOut (t b.1))
  else if j = 1 then secondLabel t (b.1, b.2.2)
    ((secondGeometry D hs hn (t b.1) (ht b.1)).yOut (t b.2.1))
  else thirdLabel (K := K) (F := F) (b.1, b.2.1)
    ((thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).yOut (t b.2.2))

/-- The physical X source agrees with stage one's actual lifted local input. -/
theorem x_source (b : GlobalCircuit.Address B) :
    xInput D hs hn t ht 0 b = source (A := A) (C := C) t (Sum.inl b) := by
  change _ = terminal t b
  simpa only [xInput, firstLabel, Fin.isValue, ↓reduceIte, terminal] using
    geometry_x_source D hs hn (t b.1) (t b.2.1) (t b.2.2)

theorem y_source (b : GlobalCircuit.Address B) :
    yInput D hs hn t ht 0 b = source (A := A) (C := C) t (Sum.inr (Sum.inl b)) := by
  change _ = ⊥
  simpa only [yInput, firstLabel, Fin.isValue, ↓reduceIte] using
    geometry_y_source D hs hn (t b.1) (t b.2.1) (t b.2.2)

/-- Stage boundary compatibility is proved at the same physical address. -/
theorem x_one_two (b : GlobalCircuit.Address B) :
    xOutput D hs hn t ht 0 b = xInput D hs hn t ht 1 b := by
  simpa [xOutput, xInput, firstLabel, secondLabel] using
    geometry_x_one_two D hs hn (t b.1) (t b.2.1) (t b.2.2) (ht b.1)

theorem x_two_three (b : GlobalCircuit.Address B) :
    xOutput D hs hn t ht 1 b = xInput D hs hn t ht 2 b := by
  simpa [xOutput, xInput, secondLabel, thirdLabel] using
    geometry_x_two_three D hs hn (t b.1) (t b.2.1) (t b.2.2) (ht b.1) (ht b.2.1)

theorem y_one_two (b : GlobalCircuit.Address B) :
    yOutput D hs hn t ht 0 b = yInput D hs hn t ht 1 b := by
  simpa [yOutput, yInput, firstLabel, secondLabel] using
    geometry_y_one_two D hs hn (t b.1) (t b.2.1) (t b.2.2) (ht b.1)

theorem y_two_three (b : GlobalCircuit.Address B) :
    yOutput D hs hn t ht 1 b = yInput D hs hn t ht 2 b := by
  simpa [yOutput, yInput, secondLabel, thirdLabel] using
    geometry_y_two_three D hs hn (t b.1) (t b.2.1) (t b.2.2) (ht b.1) (ht b.2.1)

theorem x_sink (b : GlobalCircuit.Address B) :
    xOutput D hs hn t ht 2 b = sink (A := A) (C := C) D t (Sum.inl b) := by
  change _ = ⊤
  simpa [xOutput, thirdLabel] using
    geometry_x_sink D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)

theorem y_sink (b : GlobalCircuit.Address B) :
    yOutput D hs hn t ht 2 b = sink (A := A) (C := C) D t (Sum.inr (Sum.inl b)) := by
  change _ = (TensorSubspace.form D (TensorSubspace.form D D)).orthogonal (terminal t b)
  simpa [yOutput, thirdLabel, terminal] using
    geometry_y_sink D hs hn (t b.1) (t b.2.1) (t b.2.2) (ht b.1) (ht b.2.1) (ht b.2.2)
end Endpoints
end IntegerMultBounds.Networks.GlobalLabels
