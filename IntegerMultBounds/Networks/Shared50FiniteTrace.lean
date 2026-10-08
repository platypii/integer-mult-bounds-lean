import IntegerMultBounds.Networks.Shared50StageFrames
import IntegerMultBounds.Networks.Shared50Certificate

/-! Restriction of actual bounded label traces to the certified finite role
bank. Every original incidence and its ordered pair of endpoint labels is
preserved, including identity pivots and repeated incidences. -/

namespace IntegerMultBounds.Networks.Shared50FiniteTrace

section Restrict
variable {L : Type*}

abbrev bounded (capacity : ℕ) (xs : List (ℕ × L)) : Prop := ∀ p ∈ xs, p.1 < capacity

def restrictUpdates (capacity : ℕ) (xs : List (ℕ × L)) (hb : bounded capacity xs) :
    List (Fin capacity × L) :=
  xs.attach.map (fun p => (⟨p.val.1,hb p.val p.property⟩,p.val.2))

theorem restrict_nil (capacity : ℕ) (hb : bounded capacity ([] : List (ℕ × L))) :
    restrictUpdates capacity [] hb = [] := rfl

theorem restrict_cons (capacity : ℕ) (p : ℕ × L) (xs : List (ℕ × L))
    (hb : bounded capacity (p::xs)) :
    restrictUpdates capacity (p::xs) hb =
      (⟨p.1,hb p (by simp)⟩,p.2) ::
        restrictUpdates capacity xs (fun q hq => hb q (by simp [hq])) := by
  simp [restrictUpdates, List.attach_cons, List.map_map]

theorem update_restrict (capacity : ℕ) (current : ℕ → L) (p : ℕ × L) (hp : p.1 < capacity) :
    (fun i : Fin capacity => Function.update current p.1 p.2 i.val) =
      Function.update (fun i : Fin capacity => current i.val) ⟨p.1,hp⟩ p.2 := by
  funext i
  by_cases hi : i.val = p.1 <;> simp [Function.update_apply, Fin.ext_iff, hi]

/-- Every finite endpoint is the restriction of the actual natural-role endpoint. -/
theorem finish_restrict (capacity : ℕ) (xs : List (ℕ × L)) (hb : bounded capacity xs)
    (current : ℕ → L) :
    RankTrace.finish (fun i : Fin capacity => current i.val) (restrictUpdates capacity xs hb) =
      fun i => RankTrace.finish current xs i.val := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    rw [restrict_cons,RankTrace.finish,← update_restrict,ih _ (Function.update current p.1 p.2)]
    rfl

/-- Restriction retains the complete ordered edge list, without filtering. -/
theorem edges_restrict (capacity : ℕ) (xs : List (ℕ × L)) (hb : bounded capacity xs)
    (current : ℕ → L) :
    RankTrace.edges (fun i : Fin capacity => current i.val) (restrictUpdates capacity xs hb) =
      RankTrace.edges current xs := by
  induction xs generalizing current with
  | nil => rfl
  | cons p xs ih =>
    rw [restrict_cons,RankTrace.edges,← update_restrict,ih _ (Function.update current p.1 p.2)]
    rfl

theorem restrict_length (capacity : ℕ) (xs : List (ℕ × L)) (hb : bounded capacity xs) :
    (restrictUpdates capacity xs hb).length = xs.length := by simp [restrictUpdates]

theorem bounded_map {M : Type*} (capacity : ℕ) (xs : List (ℕ × L)) (hb : bounded capacity xs)
    (f : L → M) : bounded capacity (xs.map (fun p => (p.1,f p.2))) := by
  rintro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hb q hq

end Restrict

open SharedPointReplay
attribute [local irreducible] circuit

/-- The actual allocator bounds declared gate incidences, including pivots
that emit no scalar instruction. Thus no label update is silently dropped. -/
theorem forward_bound : bounded 509194 Shared50Frames.updates := by
  intro p hp
  obtain ⟨event,he,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨role,hr,heq⟩ := List.mem_map.mp hp
  have he' : event.gate ∈ SharedPointExecution.code.gates := by
    rw [← Shared50Frames.events_erasure]
    exact List.mem_map.mpr ⟨event,he,rfl⟩
  have hb := DAGAllocator.compile_gates_bounded circuit.nodes outputRefs valid outputRefs_bounds event.gate he'
  have hh := (hb role hr).trans_le Shared50Certificate.role_bound
  exact heq ▸ hh

/-- Every lifted stage label retains its actual certified role bound. -/
theorem stage_bound {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    bounded 509194 (Shared50StageFrames.mapUpdates f Shared50Frames.updates) :=
  bounded_map _ _ forward_bound f

/-- Actual finite forward trace with any chosen stage label lift. -/
def forward {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) : List (Fin 509194 × L) :=
  restrictUpdates 509194 (Shared50StageFrames.mapUpdates f Shared50Frames.updates) (stage_bound f)

theorem forward_finish {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    RankTrace.finish (fun i : Fin 509194 => f (Shared50Frames.initialLabels i.val)) (forward f) =
      fun i => f (Shared50Frames.finalLabels i.val) := by
  rw [forward, finish_restrict _ _ _ (fun i => f (Shared50Frames.initialLabels i))]
  have hh := Shared50StageFrames.finish_map f Shared50Frames.initialLabels Shared50Frames.updates
  exact congrArg (fun g => fun i : Fin 509194 => g i.val) hh

theorem forward_edges {L : Type*} (f : Submodule ℚ (Fin 50 → ℚ) → L) :
    RankTrace.edges (fun i : Fin 509194 => f (Shared50Frames.initialLabels i.val)) (forward f) =
      (RankTrace.edges Shared50Frames.initialLabels Shared50Frames.updates).map (fun p => (f p.1,f p.2)) := by
  rw [forward, edges_restrict _ _ _ (fun i => f (Shared50Frames.initialLabels i)), Shared50StageFrames.edges_map]

end IntegerMultBounds.Networks.Shared50FiniteTrace
