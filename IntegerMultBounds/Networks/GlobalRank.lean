import IntegerMultBounds.Networks.GlobalLabels

/-! Rank accounting through the actual physical placements and tensor-stage
label transports. No local loss or history is supplied as an oracle. -/

namespace IntegerMultBounds.Networks.GlobalRank

open GroupedCircuit GroupedFrames GlobalLabels LabeledMotif
open Module
open scoped TensorProduct

section Placement
variable {ι κ L M R : Type*} [DecidableEq ι] [DecidableEq κ] [CommRing R] [DecidableEq R]

/-- A placed invocation has no label incidences outside its actual image. -/
theorem history_place_outside (f : ι ↪ κ) (labelMap : L → M) (vs : List (Vertex ι L R))
    (k : κ) (hk : ∀ i, f i ≠ k) : history (placeList f labelMap vs) k = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  have hnot : k ∉ touched (place f labelMap w).group := by
    rw [← mem_support]
    change k ∉ support (GlobalGrouped.embedGroup f w.group)
    rw [GlobalGrouped.support_embed]
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun i _ => hk i
  simp [hnot]

theorem pathLoss_map (d : L → ℕ) (e : M → ℕ) (f : L → M)
    (hd : ∀ l, e (f l) = d l) (current : L) (xs : List L) :
    pathLoss e (f current) (xs.map f) = pathLoss d current xs := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih => simp [pathLoss, hd, ih]

/-- Reducing only the initial dimension cannot increase the path's loss. -/
theorem pathLoss_mono_start (d : L → ℕ) (x y : L) (h : d x ≤ d y) (xs : List L) :
    pathLoss d x xs ≤ pathLoss d y xs := by
  cases xs with
  | nil => exact le_rfl
  | cons l ls => exact Nat.add_le_add_right (Nat.sub_le_sub_right h _) _

theorem pathRel_map (rel : L → L → Prop) (rel' : M → M → Prop) (f : L → M)
    (hr : ∀ x y, rel x y → rel' (f x) (f y)) (current : L) (xs : List L)
    (h : pathRel rel current xs) : pathRel rel' (f current) (xs.map f) := by
  induction xs generalizing current with
  | nil => trivial
  | cons l ls ih => exact ⟨hr current l h.1, ih l h.2⟩

omit [DecidableEq ι] in
/-- Finite sums over a physical embedding ignore registers outside its image. -/
theorem sum_embedding [Fintype ι] [Fintype κ] (f : ι ↪ κ) (v : κ → ℕ)
    (hv : ∀ k, (∀ i, f i ≠ k) → v k = 0) : ∑ k, v k = ∑ i, v (f i) := by
  classical
  calc
    _ = ∑ k ∈ Finset.univ.image f, v k := by
      symm
      apply Finset.sum_subset (by simp)
      intro k _ hk
      exact hv k (by simpa using hk)
    _ = _ := Finset.sum_image (fun _ _ _ _ h => f.injective h)

/-- Exact loss is unchanged by dimension-preserving label transport and
injective physical placement, for a matching input on every local register. -/
theorem loss_place [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (labelMap : L → M) (d : L → ℕ) (e : M → ℕ)
    (hd : ∀ l, e (labelMap l) = d l) (localInput : ι → L) (current : κ → M)
    (hi : ∀ i, current (f i) = labelMap (localInput i)) (vs : List (Vertex ι L R)) :
    RankTrace.loss e current (updates (placeList f labelMap vs)) =
      RankTrace.loss d localInput (updates vs) := by
  rw [loss_history, loss_history, sum_embedding f]
  · apply Finset.sum_congr rfl
    intro i _
    rw [history_place, hi, pathLoss_map d e labelMap hd]
  · intro k hk
    rw [history_place_outside f labelMap vs k hk]
    rfl

/-- The actual invocation loss is bounded by the proved local loss even when
preceding sparse stages leave smaller input labels. -/
theorem loss_place_le [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (labelMap : L → M) (d : L → ℕ) (e : M → ℕ)
    (hd : ∀ l, e (labelMap l) = d l) (localInput : ι → L) (current : κ → M)
    (hi : ∀ i, e (current (f i)) ≤ d (localInput i)) (vs : List (Vertex ι L R)) :
    RankTrace.loss e current (updates (placeList f labelMap vs)) ≤
      RankTrace.loss d localInput (updates vs) := by
  rw [loss_history, loss_history, sum_embedding f]
  · apply Finset.sum_le_sum
    intro i _
    rw [history_place]
    calc
      _ ≤ pathLoss e (labelMap (localInput i)) ((history vs i).map labelMap) :=
        pathLoss_mono_start e _ _ (by rw [hd]; exact hi i) _
      _ = _ := pathLoss_map d e labelMap hd _ _
  · intro k hk
    rw [history_place_outside f labelMap vs k hk]
    rfl

/-- Actual placed traces preserve any reflexive relation transported by the
label map; outsiders have no edges at all. -/
theorem comparable_place (f : ι ↪ κ) (labelMap : L → M)
    (rel : L → L → Prop) (rel' : M → M → Prop) (hrefl : ∀ l, rel' l l)
    (hr : ∀ x y, rel x y → rel' (labelMap x) (labelMap y))
    (localInput : ι → L) (current : κ → M)
    (hi : ∀ i, current (f i) = labelMap (localInput i)) (vs : List (Vertex ι L R))
    (hh : ∀ i, pathRel rel (localInput i) (history vs i)) :
    ∀ p ∈ RankTrace.edges current (updates (placeList f labelMap vs)), rel' p.1 p.2 := by
  apply edges_history_rel rel' hrefl
  intro k
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [history_place, hi]
    exact pathRel_map rel rel' labelMap hr _ _ (hh i)
  · rw [history_place_outside f labelMap vs k (by simpa using hk)]
    trivial

section Ordered
variable [Preorder L] [Preorder M]

theorem pathRel_weak_start (lower upper : L) (xs : List L) (hle : lower ≤ upper)
    (hfirst : ∀ l ∈ xs, upper ≤ l)
    (hh : pathRel (fun x y => x ≤ y ∨ y ≤ x) upper xs) :
    pathRel (fun x y => x ≤ y ∨ y ≤ x) lower xs := by
  cases xs with
  | nil => trivial
  | cons l ls => exact ⟨Or.inl (hle.trans (hfirst l (by simp))), hh.2⟩

/-- Sparse earlier stages may leave smaller labels. Actual first edges still
increase, and later edges are the already proved local ones. -/
theorem comparable_place_le (f : ι ↪ κ) (labelMap : L → M) (hm : Monotone labelMap)
    (localInput : ι → L) (current : κ → M)
    (hi : ∀ i, current (f i) ≤ labelMap (localInput i)) (vs : List (Vertex ι L R))
    (hall : ∀ i l, l ∈ history vs i → localInput i ≤ l)
    (hh : ∀ i, pathRel (fun x y => x ≤ y ∨ y ≤ x) (localInput i) (history vs i)) :
    ∀ p ∈ RankTrace.edges current (updates (placeList f labelMap vs)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  apply edges_history_rel (fun x y : M => x ≤ y ∨ y ≤ x) (fun _ => Or.inl le_rfl)
  intro k
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [history_place]
    apply pathRel_weak_start _ (labelMap (localInput i)) _ (hi i)
    · intro l hl
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
      exact hm (hall i u hu)
    · exact pathRel_map _ _ labelMap
        (fun x y h => h.elim (fun h => Or.inl (hm h)) (fun h => Or.inr (hm h))) _ _ (hh i)
  · rw [history_place_outside f labelMap vs k (by simpa using hk)]
    trivial

theorem getLastD_mono (xs : List M) (x y : M) (h : x ≤ y) :
    xs.getLast?.getD x ≤ xs.getLast?.getD y := by
  cases xs with
  | nil => exact h
  | cons l ls => simp [List.getLast?_eq_some_getLast (List.cons_ne_nil l ls)]

/-- Final labels under physical placement inherit the local endpoint bound,
even when the actual starting labels are smaller than the canonical ones. -/
theorem finalLabels_place_le (f : ι ↪ κ) (labelMap : L → M) (hm : Monotone labelMap)
    (localInput localOutput : ι → L) (current : κ → M)
    (hi : ∀ i, current (f i) ≤ labelMap (localInput i)) (vs : List (Vertex ι L R))
    (hf : ∀ i, finalLabels localInput vs i ≤ localOutput i) (i : ι) :
    finalLabels current (placeList f labelMap vs) (f i) ≤ labelMap (localOutput i) := by
  rw [finalLabels_history, history_place]
  calc
    _ ≤ ((history vs i).map labelMap).getLast?.getD (labelMap (localInput i)) :=
      getLastD_mono _ _ _ (hi i)
    _ = labelMap (finalLabels localInput vs i) := by
      rw [finalLabels_history]
      cases hx : (history vs i).getLast? <;> simp [List.getLast?_map, hx]
    _ ≤ _ := hm (hf i)

end Ordered

/-- Untouched physical registers retain their actual preceding label. -/
theorem finalLabels_place_outside (f : ι ↪ κ) (labelMap : L → M) (vs : List (Vertex ι L R))
    (current : κ → M) (k : κ) (hk : ∀ i, f i ≠ k) :
    finalLabels current (placeList f labelMap vs) k = current k := by
  rw [finalLabels_history, history_place_outside f labelMap vs k hk]
  rfl

end Placement

section LocalInputs
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s : ℕ}
variable (g : MotifLabels.Geometry K E F) (t : Fin n → F)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Every local forward label seen by a wire contains that wire's input.
This is stronger than first-edge comparability and handles arbitrary omissions. -/
theorem forward_input_le_history (i : Circuit.Role n a c s) (U : Submodule K (E ⊗[K] F))
    (hU : U ∈ history (forward g t owner G J H) i) : input g t i ≤ U := by
  rcases i with j | j | j
  · change U ∈ history _ (Circuit.x j) at hU
    rw [forward_x_history] at hU
    change g.xIn (t j) ≤ U
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := h₁.trans (g.middle_le_full (t j))
    split_ifs at hU <;> simp_all <;> aesop
  · change U ∈ history _ (Circuit.y j) at hU
    rw [forward_y_history] at hU
    change g.yIn (t j) ≤ U
    have h₁ := g.yIn_le_common (t j)
    have h₂ := h₁.trans (g.common_le_yOut (t j))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
    aesop
  · exact bot_le

theorem inverse_input_le_history (i : Circuit.Role n a c s) (U : Submodule K (E ⊗[K] F))
    (hU : U ∈ history (inverse g t owner G J H) i) : inverseInput g t i ≤ U := by
  rcases i with j | j | j
  · change U ∈ history _ (Circuit.x j) at hU
    rw [inverse_x_history] at hU
    change g.yIn (t j) ≤ U
    have h₁ := g.yIn_le_common (t j)
    have h₂ := h₁.trans (g.common_le_yOut (t j))
    split_ifs at hU <;> simp_all <;> aesop
  · change U ∈ history _ (Circuit.y j) at hU
    rw [inverse_y_history] at hU
    change g.xIn (t j) ≤ U
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := h₁.trans (g.middle_le_full (t j))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
    aesop
  · exact bot_le

theorem opposite_input_le_history (i : Circuit.Role n a c s) (U : Submodule K (E ⊗[K] F))
    (hU : U ∈ history (opposite g t owner G J H) i) : input g t i ≤ U := by
  obtain ⟨i, rfl⟩ := (Circuit.exchangeRoles n a c s).surjective i
  rw [opposite_history] at hU
  have hi : input g t (Circuit.exchangeRoles n a c s i) = inverseInput g t i := by
    rcases i with j | j | j <;> rfl
  rw [hi]
  exact inverse_input_le_history g t owner G J H i U hU

end LocalInputs

section StageTransport
variable {K F B : Type*} [Field K] [AddCommGroup F] [Module K F] [FiniteDimensional K F]
variable (D : LinearMap.BilinForm K F) (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

include D ht in
theorem firstLabel_finrank (q : B × B) (U : Submodule K (K ⊗[K] F)) :
    finrank K (firstLabel t q U) = finrank K U := by
  rw [firstLabel, LinearEquiv.finrank_map_eq]
  apply MotifLabels.Geometry.liftLabel_finrank (TensorSubspace.form D D)
  simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
    mul_ne_zero (ht q.2) (ht q.1)

include D ht in
theorem secondLabel_finrank (q : B × B) (U : Submodule K (F ⊗[K] F)) :
    finrank K (secondLabel t q U) = finrank K U := by
  rw [secondLabel, LinearEquiv.finrank_map_eq]
  exact MotifLabels.Geometry.liftLabel_finrank D _ (ht q.2) U

theorem thirdLabel_finrank (q : B × B) (U : Submodule K ((F ⊗[K] F) ⊗[K] F)) :
    finrank K (thirdLabel (K := K) (F := F) q U) = finrank K U := by
  rw [thirdLabel, LinearEquiv.finrank_map_eq]
  apply MotifLabels.Geometry.liftLabel_finrank (StageLabels.unitForm : LinearMap.BilinForm K K)
  simp [StageLabels.unitForm]

omit [FiniteDimensional K F] in
theorem firstLabel_mono (q : B × B) : Monotone (firstLabel (K := K) t q) := by
  intro U V h
  exact Submodule.map_mono (MotifLabels.Geometry.liftLabel_mono _ h)

omit [FiniteDimensional K F] in
theorem secondLabel_mono (q : B × B) : Monotone (secondLabel (K := K) t q) := by
  intro U V h
  exact Submodule.map_mono (MotifLabels.Geometry.liftLabel_mono _ h)

omit [FiniteDimensional K F] in
theorem thirdLabel_mono (q : B × B) : Monotone (thirdLabel (K := K) (F := F) q) := by
  intro U V h
  exact Submodule.map_mono (MotifLabels.Geometry.liftLabel_mono _ h)

end StageTransport
section Invocations
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c : ℕ}
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Canonical local input of an actual physical invocation, expressed in the
common cube. Its actual preceding labels are allowed to be smaller. -/
def invocationInput (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    Submodule K (StageLabels.Ambient K F) :=
  if j = 0 then firstLabel t q (input (StageLabels.firstGeometry D hs hn) (t ∘ eB) i)
  else if j = 1 then secondLabel t q
    (input (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) i)
  else thirdLabel (K := K) (F := F) q
    (input (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) i)

/-- Canonical completed local output, before raising scratch to the full cube. -/
def invocationOutput (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    Submodule K (StageLabels.Ambient K F) :=
  if j = 0 then firstLabel t q (output (StageLabels.firstGeometry D hs hn) (t ∘ eB) i)
  else if j = 1 then secondLabel t q
    (output (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) i)
  else thirdLabel (K := K) (F := F) q
    (output (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) i)

variable [Fintype B] [Fintype A] [Fintype C]

/-- The actual placed invocation, with its actual preceding labels, loses at
most one current-factor dimension per central register. -/
theorem invocation_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (q : B × B) (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      current (updates (invocation D hs hn t ht eB eA eC owner G J H j q)) ≤ c * finrank K F := by
  fin_cases j
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun U : Submodule K (K ⊗[K] F) => finrank K U)
          (input (StageLabels.firstGeometry D hs hn) (t ∘ eB))
          (updates (forward (StageLabels.firstGeometry D hs hn) (t ∘ eB) owner G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 0 q) (firstLabel t q)
          _ _ (firstLabel_finrank D t ht q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [firstLabel_finrank D t ht q] at hd
      _ ≤ _ := forward_loss_le (StageLabels.firstGeometry D hs hn) (t ∘ eB) owner G J H target hJ hneigh
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun U : Submodule K (F ⊗[K] F) => finrank K U)
          (input (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB))
          (updates (opposite (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 1 q) (secondLabel t q)
          _ _ (secondLabel_finrank D t ht q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [secondLabel_finrank D t ht q] at hd
      _ ≤ _ := opposite_loss_le (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H target hJ (fun p => by
        change D (t (eB (target p))) (t (eB (owner p))) = 0
        rw [hs.eq, hneigh p])
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    calc
      _ ≤ RankTrace.loss (fun U : Submodule K ((F ⊗[K] F) ⊗[K] F) => finrank K U)
          (input (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB))
          (updates (forward (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) owner G J H)) := by
        apply loss_place_le (GlobalCircuit.localEmbedding eB eA eC 2 q) (thirdLabel (K := K) (F := F) q)
          _ _ (thirdLabel_finrank (K := K) (F := F) q)
        intro i
        have hd := Submodule.finrank_mono (hcur i)
        rwa [thirdLabel_finrank (K := K) (F := F) q] at hd
      _ ≤ _ := forward_loss_le (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) owner G J H target hJ hneigh

omit [Fintype B] [Fintype A] [Fintype C] in
/-- Every actual placed edge is comparable even when the preceding stage
leaves a smaller input label because a scalar incidence is absent. -/
theorem invocation_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (q : B × B) (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) :
    ∀ p ∈ RankTrace.edges current (updates (invocation D hs hn t ht eB eA eC owner G J H j q)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  fin_cases j
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 0 q) (firstLabel t q)
      (firstLabel_mono t q) (input (StageLabels.firstGeometry D hs hn) (t ∘ eB)) current hcur
    · exact forward_input_le_history (StageLabels.firstGeometry D hs hn) (t ∘ eB) owner G J H
    · exact forward_histories_comparable (StageLabels.firstGeometry D hs hn) (t ∘ eB) owner G J H target hJ hneigh
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 1 q) (secondLabel t q)
      (secondLabel_mono t q) (input (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB)) current hcur
    · exact opposite_input_le_history (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H
    · exact opposite_histories_comparable (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H target hJ (fun p => by
        change D (t (eB (target p))) (t (eB (owner p))) = 0
        rw [hs.eq, hneigh p])
  · simp [invocation, invocationInput, -Sum.forall, -Prod.forall] at hcur ⊢
    apply comparable_place_le (GlobalCircuit.localEmbedding eB eA eC 2 q) (thirdLabel (K := K) (F := F) q)
      (thirdLabel_mono (K := K) (F := F) q) (input (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB)) current hcur
    · exact forward_input_le_history (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) owner G J H
    · exact forward_histories_comparable (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) owner G J H target hJ hneigh

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The completed local output bounds the actual physical labels after the
invocation, with no artificial alignment inserted into the scalar schedule. -/
theorem invocation_final_le (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput D hs hn t ht eB j q i) (i : Circuit.Role n a c 0) :
    finalLabels current (invocation D hs hn t ht eB eA eC owner G J H j q)
      (GlobalCircuit.localEmbedding eB eA eC j q i) ≤ invocationOutput D hs hn t ht eB j q i := by
  fin_cases j
  · simp [invocation, invocationInput, invocationOutput, -Sum.forall, -Prod.forall] at hcur ⊢
    exact finalLabels_place_le (GlobalCircuit.localEmbedding eB eA eC 0 q) (firstLabel t q)
      (firstLabel_mono t q) (input (StageLabels.firstGeometry D hs hn) (t ∘ eB)) (output (StageLabels.firstGeometry D hs hn) (t ∘ eB)) current hcur _
      (forward_final_le_output (StageLabels.firstGeometry D hs hn) (t ∘ eB) owner G J H) i
  · simp [invocation, invocationInput, invocationOutput, -Sum.forall, -Prod.forall] at hcur ⊢
    exact finalLabels_place_le (GlobalCircuit.localEmbedding eB eA eC 1 q) (secondLabel t q)
      (secondLabel_mono t q) (input (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB)) (output (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB)) current hcur _
      (opposite_final_le_output (StageLabels.secondGeometry D hs hn (t q.1) (ht q.1)) (t ∘ eB) owner G J H) i
  · simp [invocation, invocationInput, invocationOutput, -Sum.forall, -Prod.forall] at hcur ⊢
    exact finalLabels_place_le (GlobalCircuit.localEmbedding eB eA eC 2 q) (thirdLabel (K := K) (F := F) q)
      (thirdLabel_mono (K := K) (F := F) q) (input (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB)) (output (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB)) current hcur _
      (forward_final_le_output (StageLabels.thirdGeometry D hs hn (t q.1) (t q.2) (ht q.1) (ht q.2)) (t ∘ eB) owner G J H) i

omit [Nontrivial R] [Fintype B] [Fintype A] [Fintype C] in
/-- Every physical register outside the invocation remains unchanged. -/
theorem invocation_final_outside (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (invocation D hs hn t ht eB eA eC owner G J H j q) k = current k := by
  fin_cases j <;> simp [invocation] <;> apply finalLabels_place_outside <;> exact hk

end Invocations

end IntegerMultBounds.Networks.GlobalRank
