module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternCoordinates

/-! The live profile generator emits exactly the mirrored absolute coordinates
used by sparse-pattern compilation. Profiles contain source choices and activity,
never prepared slot positions or source-selector increments. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {A W m N : ℕ}

def affineProfileTargets (i k o N : ℕ) : List (Bool × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (enabled, q) :: rest => (N - 1 - (i * k + o), if enabled then q + 1 else 0) ::
      affineProfileTargets (i + 1) k o N rest

theorem sparseCoordinateFrames_append (L Ls : ℕ) (xs ys : List (ℕ × ℕ)) :
    sparseCoordinateFrames (A := A) L Ls (xs ++ ys) =
      sparseCoordinateFrames L Ls xs ++ sparseCoordinateFrames L Ls ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [sparseCoordinateFrames, ih]

theorem affineProfileOutput_frames (Li Lk Ls i k o N : ℕ) (entries : List (Bool × ℕ)) :
    affineProfileOutput (A := A) Li Lk Ls i k o N entries =
      sparseCoordinateFrames (Li + Lk) Ls (affineProfileTargets i k o N entries).reverse := by
  induction entries generalizing i with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨enabled, q⟩ := pair
    simp [affineProfileOutput, affineProfileTargets, List.reverse_cons,
      sparseCoordinateFrames_append, sparseCoordinateFrames, ih]

theorem affineProfileTargets_ofFn (i k o N : ℕ) (f : Fin m → Bool × ℕ) :
    affineProfileTargets i k o N (List.ofFn f) = List.ofFn (fun j =>
      (N - 1 - ((i + j.val) * k + o), if (f j).1 then (f j).2 + 1 else 0)) := by
  induction m generalizing i with
  | zero => simp [affineProfileTargets]
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    obtain ⟨enabled, q⟩ := f 0
    simp only [affineProfileTargets]
    rw [ih]
    congr 1
    apply congrArg List.ofFn
    funext j
    simp [Nat.add_assoc, Nat.add_comm 1]

def affineSourceProfile (src : Fin m → Option (Fin W)) : List (Bool × ℕ) :=
  List.ofFn (fun j => (src j).elim (false, 0) (fun q => (true, q.val)))

theorem affineProfileReady_ofFn (Li Ls i k o N : ℕ) (f : Fin m → Bool × ℕ)
    (h : ∀ j, i + j.val < 2 ^ Li ∧ (i + j.val) * k + o < N ∧ (f j).2 + 1 < 2 ^ Ls) :
    AffineProfileReady Li Ls k o N i (List.ofFn f) := by
  induction m generalizing i with
  | zero => trivial
  | succ m ih =>
    rw [List.ofFn_succ]
    have hh := h 0
    rcases hp : f 0 with ⟨enabled, q⟩
    change i < 2 ^ Li ∧ i * k + o < N ∧ q + 1 < 2 ^ Ls ∧ _
    refine ⟨by simpa using hh.1, by simpa using hh.2.1, by simpa only [hp] using hh.2.2, ?_⟩
    apply ih
    intro j
    simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h j.succ

theorem affineSourceProfile_ready (Li Ls i k o : ℕ) (src : Fin m → Option (Fin W))
    (hi : i + m ≤ 2 ^ Li) (hpos : ∀ j : Fin m, (i + j.val) * k + o < N)
    (hW : W + 1 < 2 ^ Ls) :
    AffineProfileReady Li Ls k o N i (affineSourceProfile src) := by
  apply affineProfileReady_ofFn
  intro j
  refine ⟨by have hj := j.isLt; omega, hpos j, ?_⟩
  cases h : src j with
  | none => simp only [Option.elim_none]; omega
  | some q => simp only [Option.elim_some]; have hq := q.isLt; omega

theorem affineProfileFrames_length (Ls : ℕ) (entries : List (Bool × ℕ)) :
    (affineProfileFrames (A := A) Ls entries).length = entries.length * (Ls + 3) := by
  induction entries with
  | nil => simp [affineProfileFrames]
  | cons pair rest ih =>
    cases pair
    simp only [affineProfileFrames, List.length_append, List.length_cons, length_binSyms, ih,
      Nat.add_mul, Nat.one_mul]
    omega

theorem affineSourceProfile_coordinates (i k o : ℕ) (src : Fin m → Option (Fin W)) :
    (affineProfileTargets i k o N (affineSourceProfile src)).reverse =
      sparseCoordinateValues (sparsePatternCoordinates (N := N) (fun j => (i + j) * k + o) src) := by
  rw [affineSourceProfile, affineProfileTargets_ofFn]
  simp only [sparsePatternCoordinates, sparseCoordinateValues, List.map_reverse, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  cases h : src j <;> simp [h]

theorem affineSourceProfile_output (Li Lk Ls i k o : ℕ) (src : Fin m → Option (Fin W)) :
    affineProfileOutput (A := A) Li Lk Ls i k o N (affineSourceProfile src) =
      sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (i + j) * k + o) src)) := by
  rw [affineProfileOutput_frames, affineSourceProfile_coordinates]

end IntegerMultBounds.MathlibTM2.Routing
