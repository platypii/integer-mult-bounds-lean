import IntegerMultBounds.Networks.GlobalRank

/-! Aggregation over actual disjoint physical invocations within a stage,
followed by the real three tensor-stage boundaries. -/

namespace IntegerMultBounds.Networks.GlobalRank

open GroupedFrames GlobalLabels LabeledMotif
open Module
open scoped TensorProduct

section Lists
variable {ι L R : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]

theorem finalLabels_append (current : ι → L) (vs ws : List (Vertex ι L R)) :
    finalLabels current (vs ++ ws) = finalLabels (finalLabels current vs) ws := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih => exact ih _

omit [DecidableEq ι] in
theorem updates_append (vs ws : List (Vertex ι L R)) :
    updates (vs ++ ws) = updates vs ++ updates ws := by simp [updates]

end Lists

section Stage
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c : ℕ}
variable (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Recover the fixed coordinate key from any physical register. -/
def physicalKey (j : Fin 3) : GlobalCircuit.World B A C → B × B
  | .inl b => GlobalCircuit.fixed j b
  | .inr (.inl b) => GlobalCircuit.fixed j b
  | .inr (.inr p) => p.1.2

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
theorem physicalKey_local (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    physicalKey j (GlobalCircuit.localEmbedding eB eA eC j q i) = q := by
  rcases i with i | i | i | i | i
  all_goals try exact Fin.elim0 i
  all_goals simp [GlobalCircuit.localEmbedding, GlobalCircuit.localMap, physicalKey]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
/-- Distinct fixed-coordinate invocations have disjoint physical registers. -/
theorem localEmbedding_disjoint (j : Fin 3) {q q' : B × B} (h : q ≠ q')
    (i i' : Circuit.Role n a c 0) :
    GlobalCircuit.localEmbedding eB eA eC j q i ≠ GlobalCircuit.localEmbedding eB eA eC j q' i' := by
  intro he
  have hh := congrArg (physicalKey (A := A) (C := C) j) he
  rw [physicalKey_local, physicalKey_local] at hh
  exact h hh

omit [Nontrivial R] in
/-- Invocations whose images omit a register preserve that register's label. -/
theorem partial_final_outside (j : Fin 3) (qs : List (B × B))
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (k : GlobalCircuit.World B A C)
    (hk : ∀ q ∈ qs, ∀ i, GlobalCircuit.localEmbedding eB eA eC j q i ≠ k) :
    finalLabels current (qs.flatMap (invocation D hs hn t ht eB eA eC owner G J H j)) k = current k := by
  induction qs generalizing current with
  | nil => rfl
  | cons q qs ih =>
    rw [List.flatMap_cons, finalLabels_append,
      ih _ (fun q' hq' => hk q' (by simp [hq']))]
    exact invocation_final_outside D hs hn t ht eB eA eC owner G J H j q current k
      (hk q (by simp))

variable [Fintype B] [Fintype A] [Fintype C]

/-- Actual loss aggregation across a duplicate-free invocation list. Later
invocation inputs are unchanged because the physical images are disjoint. -/
theorem partial_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      current (updates (qs.flatMap (invocation D hs hn t ht eB eA eC owner G J H j))) ≤
      qs.length * (c * finrank K F) := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.loss, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i,
        finalLabels current (invocation D hs hn t ht eB eA eC owner G J H j q)
          (GlobalCircuit.localEmbedding eB eA eC j q' i) ≤ invocationInput (a := a) (c := c) D hs hn t ht eB j q' i := by
      intro q' hq' i
      rw [invocation_final_outside D hs hn t ht eB eA eC owner G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    have hfirst := invocation_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh
      j q current (hcur q (by simp))
    have htail := ih hnodup.2 _ hrest
    rw [List.flatMap_cons, updates_append, loss_append, ← finalLabels_trace]
    simp only [List.length_cons, Nat.add_mul, one_mul]
    omega

omit [Fintype B] [Fintype A] [Fintype C] in
/-- Every actual edge of the partial physical stage is comparable. -/
theorem partial_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) :
    ∀ p ∈ RankTrace.edges current
      (updates (qs.flatMap (invocation D hs hn t ht eB eA eC owner G J H j))),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i,
        finalLabels current (invocation D hs hn t ht eB eA eC owner G J H j q)
          (GlobalCircuit.localEmbedding eB eA eC j q' i) ≤ invocationInput (a := a) (c := c) D hs hn t ht eB j q' i := by
      intro q' hq' i
      rw [invocation_final_outside D hs hn t ht eB eA eC owner G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    intro p hp
    rw [List.flatMap_cons, updates_append, RankTrace.edges_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact invocation_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh
        j q current (hcur q (by simp)) p hp
    · rw [← finalLabels_trace] at hp
      exact ih hnodup.2 _ hrest p hp

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The last invocation touching a register supplies its actual output bound;
all other fixed-coordinate invocations preserve that register. -/
theorem partial_final_le (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ q ∈ qs, ∀ i, current (GlobalCircuit.localEmbedding eB eA eC j q i) ≤
      invocationInput (a := a) (c := c) D hs hn t ht eB j q i) (q : B × B) (hmem : q ∈ qs) (i : Circuit.Role n a c 0) :
    finalLabels current (qs.flatMap (invocation D hs hn t ht eB eA eC owner G J H j))
      (GlobalCircuit.localEmbedding eB eA eC j q i) ≤ invocationOutput (a := a) (c := c) D hs hn t ht eB j q i := by
  induction qs generalizing current with
  | nil => simp at hmem
  | cons q' qs ih =>
    have hnodup := List.nodup_cons.mp hq
    rw [List.flatMap_cons, finalLabels_append]
    by_cases he : q = q'
    · subst q'
      rw [partial_final_outside D hs hn t ht eB eA eC owner G J H j qs _ _]
      · exact invocation_final_le D hs hn t ht eB eA eC owner G J H j q current
          (hcur q (by simp)) i
      · intro q' hq' i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    · apply ih hnodup.2 _ _ ((List.mem_cons.mp hmem).resolve_left he)
      intro q'' hq'' i'
      rw [invocation_final_outside D hs hn t ht eB eA eC owner G J H j q' current _]
      · exact hcur q'' (by simp [hq'']) i'
      · intro i''
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q''; exact hnodup.1 hq'') i'' i'

/-- Stage input profile: preceding scratch stages may already be full, while
this stage and all future scratch registers still start at zero. -/
def profileInput (j : Fin 3) : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F)
  | .inl b => xInput D hs hn t ht j b
  | .inr (.inl b) => yInput D hs hn t ht j b
  | .inr (.inr p) => if p.1.1 < j then ⊤ else ⊥

/-- Stage output profile preserves future scratch at zero and completes this
stage's scratch to the ambient cube. -/
def profileOutput (j : Fin 3) : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F)
  | .inl b => xOutput D hs hn t ht j b
  | .inr (.inl b) => yOutput D hs hn t ht j b
  | .inr (.inr p) => if p.1.1 ≤ j then ⊤ else ⊥

omit [FiniteDimensional K F] [DecidableEq B] [Fintype B] in
private theorem firstLabel_bot (q : B × B) :
    firstLabel (K := K) t q ⊥ = ⊥ := by
  unfold firstLabel MotifLabels.Geometry.liftLabel
  rw [StageLabels.space_bot_left, Submodule.map_bot]

omit [FiniteDimensional K F] [DecidableEq B] [Fintype B] in
private theorem secondLabel_bot (q : B × B) :
    secondLabel (K := K) t q ⊥ = ⊥ := by
  unfold secondLabel MotifLabels.Geometry.liftLabel
  rw [StageLabels.space_bot_left, Submodule.map_bot]

omit [FiniteDimensional K F] [DecidableEq B] [Fintype B] in
private theorem thirdLabel_bot (q : B × B) :
    thirdLabel (K := K) (F := F) q ⊥ = ⊥ := by
  unfold thirdLabel MotifLabels.Geometry.liftLabel
  rw [StageLabels.space_bot_left, Submodule.map_bot]


omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem profileInput_local_x (j : Fin 3) (q : B × B) (i : Fin n) :
    profileInput (A := A) (C := C) D hs hn t ht j
      (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.x i)) =
      invocationInput (a := a) (c := c) D hs hn t ht eB j q (Circuit.x i) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileInput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.x,
      GlobalCircuit.address, invocationInput, xInput, input,
      h₀, h₁]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem profileInput_local_y (j : Fin 3) (q : B × B) (i : Fin n) :
    profileInput (A := A) (C := C) D hs hn t ht j
      (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.y i)) =
      invocationInput (a := a) (c := c) D hs hn t ht eB j q (Circuit.y i) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileInput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.y,
      GlobalCircuit.address, invocationInput, yInput, input,
      h₀, h₁]

omit [DecidableEq A] [DecidableEq C] [Fintype A] [Fintype C] [DecidableEq B] [Fintype B] in
private theorem profileInput_local_side (j : Fin 3) (q : B × B) (i : Fin a) :
    profileInput (A := A) (C := C) D hs hn t ht j
      (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.side i)) =
      invocationInput (a := a) (c := c) D hs hn t ht eB j q (Circuit.side i) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileInput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.side,
      invocationInput, input,
      firstLabel_bot, secondLabel_bot, thirdLabel_bot, h₀, h₁]

omit [DecidableEq A] [DecidableEq C] [Fintype A] [Fintype C] [DecidableEq B] [Fintype B] in
private theorem profileInput_local_center (j : Fin 3) (q : B × B) (i : Fin c) :
    profileInput (A := A) (C := C) D hs hn t ht j
      (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.center i)) =
      invocationInput (a := a) (c := c) D hs hn t ht eB j q (Circuit.center i) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileInput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.center,
      invocationInput, input,
      firstLabel_bot, secondLabel_bot, thirdLabel_bot, h₀, h₁]

omit [DecidableEq A] [DecidableEq C] [Fintype A] [Fintype C] [DecidableEq B] [Fintype B] in
/-- Restricting the stage input profile recovers the actual local cube input. -/
theorem profileInput_local (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    profileInput (A := A) (C := C) D hs hn t ht j
      (GlobalCircuit.localEmbedding eB eA eC j q i) = invocationInput (a := a) (c := c) D hs hn t ht eB j q i := by
  rcases i with i | i | i | i | i
  · exact profileInput_local_x D hs hn t ht eB eA eC j q i
  · exact profileInput_local_y D hs hn t ht eB eA eC j q i
  · exact profileInput_local_side D hs hn t ht eB eA eC j q i
  · exact profileInput_local_center D hs hn t ht eB eA eC j q i
  · exact Fin.elim0 i

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem invocationOutput_le_profile_x (j : Fin 3) (q : B × B) (i : Fin n) :
    invocationOutput (a := a) (c := c) D hs hn t ht eB j q (Circuit.x i) ≤
      profileOutput (A := A) (C := C) D hs hn t ht j
        (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.x i)) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.x,
      GlobalCircuit.address, invocationOutput, xOutput, output,
      MotifLabels.Geometry.full_eq_top, h₀, h₁]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem invocationOutput_le_profile_y (j : Fin 3) (q : B × B) (i : Fin n) :
    invocationOutput (a := a) (c := c) D hs hn t ht eB j q (Circuit.y i) ≤
      profileOutput (A := A) (C := C) D hs hn t ht j
        (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.y i)) := by
  by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
    simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.y,
      GlobalCircuit.address, invocationOutput, yOutput, output,
      h₀, h₁]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem invocationOutput_le_profile_side (j : Fin 3) (q : B × B) (i : Fin a) :
    invocationOutput (a := a) (c := c) D hs hn t ht eB j q (Circuit.side i) ≤
      profileOutput (A := A) (C := C) D hs hn t ht j
        (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.side i)) := by
  simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.side]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
private theorem invocationOutput_le_profile_center (j : Fin 3) (q : B × B) (i : Fin c) :
    invocationOutput (a := a) (c := c) D hs hn t ht eB j q (Circuit.center i) ≤
      profileOutput (A := A) (C := C) D hs hn t ht j
        (GlobalCircuit.localEmbedding eB eA eC j q (Circuit.center i)) := by
  simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.center]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
/-- Each completed local output is contained in the stage's physical output
profile. Scratch completion is monotone. -/
theorem invocationOutput_le_profile (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    invocationOutput (a := a) (c := c) D hs hn t ht eB j q i ≤
      profileOutput (A := A) (C := C) D hs hn t ht j
        (GlobalCircuit.localEmbedding eB eA eC j q i) := by
  rcases i with i | i | i | i | i
  · exact invocationOutput_le_profile_x D hs hn t ht eB eA eC j q i
  · exact invocationOutput_le_profile_y D hs hn t ht eB eA eC j q i
  · exact invocationOutput_le_profile_side D hs hn t ht eB eA eC j q i
  · exact invocationOutput_le_profile_center D hs hn t ht eB eA eC j q i
  · exact Fin.elim0 i

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
/-- Stage input labels are below their declared stage outputs. -/
theorem profileInput_le_output (j : Fin 3) (k : GlobalCircuit.World B A C) :
    profileInput D hs hn t ht j k ≤ profileOutput D hs hn t ht j k := by
  rcases k with b | b | p
  · change xInput D hs hn t ht j b ≤ xOutput D hs hn t ht j b
    fin_cases j
    · exact firstLabel_mono t _ ((StageLabels.firstGeometry D hs hn).xIn_le_middle _ |>.trans
        ((StageLabels.firstGeometry D hs hn).middle_le_full _))
    · exact secondLabel_mono t _ ((StageLabels.secondGeometry D hs hn (t b.1) (ht b.1)).xIn_le_middle _ |>.trans
        ((StageLabels.secondGeometry D hs hn (t b.1) (ht b.1)).middle_le_full _))
    · exact thirdLabel_mono (b.1, b.2.1) ((StageLabels.thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).xIn_le_middle _ |>.trans
        ((StageLabels.thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).middle_le_full _))
  · change yInput D hs hn t ht j b ≤ yOutput D hs hn t ht j b
    fin_cases j
    · exact firstLabel_mono t _ ((StageLabels.firstGeometry D hs hn).yIn_le_common _ |>.trans
        ((StageLabels.firstGeometry D hs hn).common_le_yOut _))
    · exact secondLabel_mono t _ ((StageLabels.secondGeometry D hs hn (t b.1) (ht b.1)).yIn_le_common _ |>.trans
        ((StageLabels.secondGeometry D hs hn (t b.1) (ht b.1)).common_le_yOut _))
    · exact thirdLabel_mono (b.1, b.2.1) ((StageLabels.thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).yIn_le_common _ |>.trans
        ((StageLabels.thirdGeometry D hs hn (t b.1) (t b.2.1) (ht b.1) (ht b.2.1)).common_le_yOut _))
  · change (if p.1.1 < j then ⊤ else ⊥) ≤ (if p.1.1 ≤ j then ⊤ else ⊥)
    split_ifs <;> simp_all [le_of_lt]

/-- The actual full physical stage obeys the local rank-loss count. -/
theorem stage_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      current (updates (stage D hs hn t ht eB eA eC owner G J H j)) ≤ n * n * (c * finrank K F) := by
  rw [stage, ← GlobalCircuit.keys_length eB]
  apply partial_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh j _ (GlobalCircuit.keys_nodup eB)
  intro q _ i
  rw [← profileInput_local D hs hn t ht eB eA eC j q i]
  exact hcur _

omit [Fintype B] [Fintype A] [Fintype C] in
theorem stage_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (j : Fin 3) (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) :
    ∀ p ∈ RankTrace.edges current (updates (stage D hs hn t ht eB eA eC owner G J H j)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  apply partial_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh j _ (GlobalCircuit.keys_nodup eB)
  intro q _ i
  rw [← profileInput_local D hs hn t ht eB eA eC j q i]
  exact hcur _

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The actual last labels of the full stage are below its physical output
profile; this is proved from the grouped schedule and disjoint placements. -/
theorem stage_final_le (j : Fin 3)
    (current : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F))
    (hcur : ∀ k, current k ≤ profileInput D hs hn t ht j k) (k : GlobalCircuit.World B A C) :
    finalLabels current (stage D hs hn t ht eB eA eC owner G J H j) k ≤ profileOutput D hs hn t ht j k := by
  by_cases hk : ∃ q i, GlobalCircuit.localEmbedding eB eA eC j q i = k
  · obtain ⟨q, i, rfl⟩ := hk
    apply (partial_final_le D hs hn t ht eB eA eC owner G J H j _ (GlobalCircuit.keys_nodup eB)
      current ?_ q (GlobalCircuit.mem_keys eB q) i).trans
      (invocationOutput_le_profile D hs hn t ht eB eA eC j q i)
    intro q' _ i'
    rw [← profileInput_local D hs hn t ht eB eA eC j q' i']
    exact hcur _
  · rw [stage, partial_final_outside D hs hn t ht eB eA eC owner G J H j _ current k]
    · exact (hcur k).trans (profileInput_le_output D hs hn t ht j k)
    · intro q _ i he
      exact hk ⟨q, i, he⟩

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
/-- The initial physical profile is the actual network source. -/
theorem profile_zero_source : profileInput (A := A) (C := C) D hs hn t ht 0 = source t := by
  funext k
  rcases k with b | b | p
  · exact GlobalLabels.x_source D hs hn t ht b
  · exact GlobalLabels.y_source D hs hn t ht b
  · simp [profileInput, source]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
/-- Real three-stage boundary matching on every physical register. -/
theorem profile_zero_one :
    profileOutput (A := A) (C := C) D hs hn t ht 0 = profileInput D hs hn t ht 1 := by
  funext k
  rcases k with b | b | p
  · exact GlobalLabels.x_one_two D hs hn t ht b
  · exact GlobalLabels.y_one_two D hs hn t ht b
  · change (if p.1.1 ≤ 0 then ⊤ else ⊥) = (if p.1.1 < 1 then ⊤ else ⊥)
    have hh : p.1.1 ≤ 0 ↔ p.1.1 < 1 := by omega
    simp only [hh]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
theorem profile_one_two :
    profileOutput (A := A) (C := C) D hs hn t ht 1 = profileInput D hs hn t ht 2 := by
  funext k
  rcases k with b | b | p
  · exact GlobalLabels.x_two_three D hs hn t ht b
  · exact GlobalLabels.y_two_three D hs hn t ht b
  · change (if p.1.1 ≤ 1 then ⊤ else ⊥) = (if p.1.1 < 2 then ⊤ else ⊥)
    have hh : p.1.1 ≤ 1 ↔ p.1.1 < 2 := by omega
    simp only [hh]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
theorem profile_two_sink : profileOutput (A := A) (C := C) D hs hn t ht 2 = sink D t := by
  funext k
  rcases k with b | b | p
  · exact GlobalLabels.x_sink D hs hn t ht b
  · exact GlobalLabels.y_sink D hs hn t ht b
  · change (if p.1.1 ≤ 2 then ⊤ else ⊥) = ⊤
    have hh : p.1.1 ≤ 2 := by omega
    simp [hh]

/-- The actual intermediate labels after the first physical stage. -/
def afterFirst : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F) :=
  finalLabels (source t) (stage D hs hn t ht eB eA eC owner G J H 0)

/-- The actual intermediate labels after the first two physical stages. -/
def afterSecond : GlobalCircuit.World B A C → Submodule K (StageLabels.Ambient K F) :=
  finalLabels (afterFirst D hs hn t ht eB eA eC owner G J H)
    (stage D hs hn t ht eB eA eC owner G J H 1)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype A] [Fintype C] in
theorem source_le_profile (k : GlobalCircuit.World B A C) :
    source t k ≤ profileInput D hs hn t ht 0 k := by
  rw [profile_zero_source]

omit [Fintype B] [Fintype A] [Fintype C] in
theorem afterFirst_le_profile (k : GlobalCircuit.World B A C) :
    afterFirst D hs hn t ht eB eA eC owner G J H k ≤ profileInput D hs hn t ht 1 k := by
  rw [← profile_zero_one]
  exact stage_final_le D hs hn t ht eB eA eC owner G J H 0 (source t)
    (source_le_profile D hs hn t ht) k

omit [Fintype B] [Fintype A] [Fintype C] in
theorem afterSecond_le_profile (k : GlobalCircuit.World B A C) :
    afterSecond D hs hn t ht eB eA eC owner G J H k ≤ profileInput D hs hn t ht 2 k := by
  rw [← profile_one_two]
  exact stage_final_le D hs hn t ht eB eA eC owner G J H 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC owner G J H) k

omit [Fintype B] [Fintype A] [Fintype C] in
/-- The actual complete three-stage labeled program respects its prescribed
terminal output subspaces. -/
theorem program_final_le_sink (k : GlobalCircuit.World B A C) :
    finalLabels (source t) (program D hs hn t ht eB eA eC owner G J H) k ≤ sink D t k := by
  rw [program, finalLabels_append, finalLabels_append, ← profile_two_sink D hs hn t ht]
  exact stage_final_le D hs hn t ht eB eA eC owner G J H 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC owner G J H) k

/-- Global loss is bounded by the three actual stages, each containing exactly
n squared disjoint physical invocations and c central registers per invocation. -/
theorem program_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
      (source (A := A) (C := C) t) (updates (program D hs hn t ht eB eA eC owner G J H)) ≤
      3 * n ^ 2 * c * finrank K F := by
  have h₀ := stage_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh 0 (source t)
    (source_le_profile D hs hn t ht)
  have h₁ := stage_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC owner G J H)
  have h₂ := stage_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC owner G J H)
  simp only [program, updates_append, loss_append, RankTrace.finish_append, ← finalLabels_trace]
  dsimp [afterFirst, afterSecond] at h₁ h₂
  calc
    _ ≤ 3 * (n * n * (c * finrank K F)) := by omega
    _ = _ := by ring

omit [Fintype B] [Fintype A] [Fintype C] in
/-- Every actual edge of the three-stage physical program has comparable
subspaces, including skipped scalar incidences at stage boundaries. -/
theorem program_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0) :
    ∀ p ∈ RankTrace.edges (source (A := A) (C := C) t)
      (updates (program D hs hn t ht eB eA eC owner G J H)), p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  have h₀ := stage_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh 0 (source t)
    (source_le_profile D hs hn t ht)
  have h₁ := stage_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh 1 _
    (afterFirst_le_profile D hs hn t ht eB eA eC owner G J H)
  have h₂ := stage_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh 2 _
    (afterSecond_le_profile D hs hn t ht eB eA eC owner G J H)
  dsimp [afterFirst, afterSecond] at h₁ h₂
  intro p hp
  simp only [program, updates_append, RankTrace.edges_append, RankTrace.finish_append, ← finalLabels_trace,
    List.mem_append, or_assoc] at hp
  rcases hp with hp | hp | hp
  · exact h₀ p hp
  · exact h₁ p hp
  · exact h₂ p hp

/-- Aligning actual final labels to the true sinks adds no decreasing edge. -/
theorem network_loss_eq (wires : List (GlobalCircuit.World B A C)) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U) (source t)
      (networkUpdates wires (sink D t) (program D hs hn t ht eB eA eC owner G J H)) =
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U) (source t)
      (updates (program D hs hn t ht eB eA eC owner G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ k : GlobalCircuit.World B A C,
      (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
        (RankTrace.finish (source t) (updates (program D hs hn t ht eB eA eC owner G J H)) k) -
        finrank K (sink D t k) = 0 := by
    intro k
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono
      (program_final_le_sink D hs hn t ht eB eA eC owner G J H k))
  simp [hz]

/-- Complete global rank-loss bound, including actual source and sink edges. -/
theorem network_loss_le (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (wires : List (GlobalCircuit.World B A C)) :
    RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U) (source t)
      (networkUpdates wires (sink D t) (program D hs hn t ht eB eA eC owner G J H)) ≤
      3 * n ^ 2 * c * finrank K F := by
  rw [network_loss_eq]
  exact program_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh

omit [Fintype B] [Fintype A] [Fintype C] in
/-- Comparability for every edge of the complete compiler trace. -/
theorem network_comparable (target : Fin a → Fin n)
    (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
    (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)
    (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ RankTrace.edges (source t)
      (networkUpdates wires (sink D t) (program D hs hn t ht eB eA eC owner G J H)),
      p.1 ≤ p.2 ∨ p.2 ≤ p.1 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact program_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh p hp
  · apply edges_endpoints_rel (fun U V : Submodule K (StageLabels.Ambient K F) => U ≤ V ∨ V ≤ U)
      (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro k _
    rw [← finalLabels_trace]
    exact Or.inl (program_final_le_sink D hs hn t ht eB eA eC owner G J H k)

end Stage
end IntegerMultBounds.Networks.GlobalRank
