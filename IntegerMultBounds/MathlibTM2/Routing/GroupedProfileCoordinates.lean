module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternCoordinates

/-! The grouped profile generator emits exactly the mirrored absolute coordinates
used by sparse-pattern compilation. Profiles contain source choices and activity,
never prepared slot positions or source-selector increments. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {A W m N : ℕ}

def groupedProfileTargets (i g k b N : ℕ) : List (Bool × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (enabled, q) :: rest => (N - 1 - (i / g * k + (i % g + b)), if enabled then q + 1 else 0) ::
      groupedProfileTargets (i + 1) g k b N rest

theorem groupedProfileOutput_frames (Li Lg Lk Ls i g k b N : ℕ) (entries : List (Bool × ℕ)) :
    groupedProfileOutput (A := A) Li Lg Lk Ls i g k b N entries =
      sparseCoordinateFrames (Li + Lk) Ls (groupedProfileTargets i g k b N entries).reverse := by
  induction entries generalizing i with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨enabled, q⟩ := pair
    simp [groupedProfileOutput, groupedProfileTargets, List.reverse_cons,
      sparseCoordinateFrames_append, sparseCoordinateFrames, ih]

theorem groupedProfileTargets_ofFn (i g k b N : ℕ) (f : Fin m → Bool × ℕ) :
    groupedProfileTargets i g k b N (List.ofFn f) = List.ofFn (fun j =>
      (N - 1 - ((i + j.val) / g * k + ((i + j.val) % g + b)), if (f j).1 then (f j).2 + 1 else 0)) := by
  induction m generalizing i with
  | zero => simp [groupedProfileTargets]
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    obtain ⟨enabled, q⟩ := f 0
    simp only [groupedProfileTargets]
    rw [ih]
    congr 1
    apply congrArg List.ofFn
    funext j
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem groupedProfileReady_ofFn (Li Ls i g k b N : ℕ) (f : Fin m → Bool × ℕ)
    (h : ∀ j, i + j.val < 2 ^ Li ∧ (i + j.val) / g * k + ((i + j.val) % g + b) < N ∧ (f j).2 + 1 < 2 ^ Ls) :
    GroupedProfileReady Li Ls g k b N i (List.ofFn f) := by
  induction m generalizing i with
  | zero => trivial
  | succ m ih =>
    rw [List.ofFn_succ]
    have hh := h 0
    rcases hp : f 0 with ⟨enabled, q⟩
    change i < 2 ^ Li ∧ i / g * k + (i % g + b) < N ∧ q + 1 < 2 ^ Ls ∧ _
    refine ⟨by simpa using hh.1, by simpa using hh.2.1, by simpa only [hp] using hh.2.2, ?_⟩
    apply ih
    intro j
    simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h j.succ

theorem groupedSourceProfile_ready (Li Ls i g k b : ℕ) (src : Fin m → Option (Fin W))
    (hi : i + m ≤ 2 ^ Li) (hpos : ∀ j : Fin m, (i + j.val) / g * k + ((i + j.val) % g + b) < N)
    (hW : W + 1 < 2 ^ Ls) :
    GroupedProfileReady Li Ls g k b N i (affineSourceProfile src) := by
  apply groupedProfileReady_ofFn
  intro j
  refine ⟨by have hj := j.isLt; omega, hpos j, ?_⟩
  cases h : src j with
  | none => simp only [Option.elim_none]; omega
  | some q => simp only [Option.elim_some]; have hq := q.isLt; omega

theorem groupedSourceProfile_coordinates (i g k b : ℕ) (src : Fin m → Option (Fin W)) :
    (groupedProfileTargets i g k b N (affineSourceProfile src)).reverse =
      sparseCoordinateValues (sparsePatternCoordinates (N := N) (fun j => (i + j) / g * k + ((i + j) % g + b)) src) := by
  rw [affineSourceProfile, groupedProfileTargets_ofFn]
  simp only [sparsePatternCoordinates, sparseCoordinateValues, List.map_reverse, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  cases h : src j <;> simp [h]

theorem groupedSourceProfile_output (Li Lg Lk Ls i g k b : ℕ) (src : Fin m → Option (Fin W)) :
    groupedProfileOutput (A := A) Li Lg Lk Ls i g k b N (affineSourceProfile src) =
      sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (i + j) / g * k + ((i + j) % g + b)) src)) := by
  rw [groupedProfileOutput_frames, groupedSourceProfile_coordinates]

end IntegerMultBounds.MathlibTM2.Routing
