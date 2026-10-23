module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateReverse

/-! Stream specifications for physical-coordinate inputs and canonical output
records. Both are fixed-width, nonempty frames, including at zero bit widths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host

def sourceCoordinateInputWords {A : ℕ} (Li Lk : ℕ) : List (ℕ × Bool) → List (Fin (A + 4))
  | [] => []
  | x :: xs => sourceCoordinateInputRecord Li Lk x.1 x.2 ++ sourceCoordinateInputWords Li Lk xs

theorem sourceCoordinateInputRecord_length {A : ℕ} (Li Lk q : ℕ) (enabled : Bool) :
    (sourceCoordinateInputRecord (A := A) Li Lk q enabled).length = Li + Lk + 3 := by
  simp [sourceCoordinateInputRecord]

theorem sourceCoordinateInputWords_length {A : ℕ} (Li Lk : ℕ) (xs : List (ℕ × Bool)) :
    (sourceCoordinateInputWords (A := A) Li Lk xs).length = xs.length * (Li + Lk + 3) := by
  induction xs with
  | nil => simp [sourceCoordinateInputWords]
  | cons x xs ih => simp [sourceCoordinateInputWords, sourceCoordinateInputRecord_length, ih, Nat.add_mul]; omega

theorem sourceCoordinateInputWords_head {A : ℕ} (Li Lk : ℕ) (xs : List (ℕ × Bool)) :
    (sourceCoordinateInputWords (A := A) Li Lk xs).head?.isSome = xs.head?.isSome := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases hb : (binSyms (Li + Lk) x.1 : List (Fin (A + 4))) <;>
      simp [sourceCoordinateInputWords, sourceCoordinateInputRecord, hb]

def sourceCoordinateOutputWords {A : ℕ} (Li Lk low high k : ℕ) (xs : List (ℕ × Bool)) : List (Fin (A + 4)) :=
  gatedSelectedSourceWords Li Lk (xs.map (fun x => sourceCoordinateChoice x.1 low high k x.2))

theorem sourceCoordinateOutputWords_length {A : ℕ} (Li Lk low high k : ℕ) (xs : List (ℕ × Bool)) :
    (sourceCoordinateOutputWords (A := A) Li Lk low high k xs).length = xs.length * (Li + (Li + Lk) + 5) := by
  simp [sourceCoordinateOutputWords, gatedSelectedSourceWords_length]

end IntegerMultBounds.MathlibTM2.Routing
