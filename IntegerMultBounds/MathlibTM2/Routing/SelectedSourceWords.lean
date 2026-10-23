module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceReverse

/-! Raw source records contain local coordinates and a region tag, rather than
computed selectors. Every record is self-delimiting and has a fixed width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host

structure SelectedSourceChoice where
  index : ℕ
  offset : ℕ
  lo : Bool
  hi : Bool
  deriving DecidableEq

namespace SelectedSourceChoice

def tag (x : SelectedSourceChoice) : Fin 4 := sourceTagIndex x.lo x.hi

def position (x : SelectedSourceChoice) (k : ℕ) (base : Fin 4 → ℕ) : ℕ :=
  x.index * k + base x.tag + x.offset

def word {A : ℕ} (x : SelectedSourceChoice) (Li Lk : ℕ) : List (Fin (A + 4)) :=
  selectedSourceRecord Li Lk x.index x.offset x.lo x.hi

theorem word_length {A : ℕ} (x : SelectedSourceChoice) (Li Lk : ℕ) :
    (x.word (A := A) Li Lk).length = Li + (Li + Lk) + 4 := by
  simp [word, selectedSourceRecord]
  omega

end SelectedSourceChoice

def selectedSourceWords {A : ℕ} (Li Lk : ℕ) : List SelectedSourceChoice → List (Fin (A + 4))
  | [] => []
  | x :: xs => x.word Li Lk ++ selectedSourceWords Li Lk xs

theorem selectedSourceWords_length {A : ℕ} (Li Lk : ℕ) (xs : List SelectedSourceChoice) :
    (selectedSourceWords (A := A) Li Lk xs).length = xs.length * (Li + (Li + Lk) + 4) := by
  induction xs with
  | nil => simp [selectedSourceWords]
  | cons x xs ih => simp [selectedSourceWords, SelectedSourceChoice.word_length, ih, Nat.add_mul]; omega

theorem selectedSourceWords_head {A : ℕ} (Li Lk : ℕ) (xs : List SelectedSourceChoice) :
    (selectedSourceWords (A := A) Li Lk xs).head?.isSome = xs.head?.isSome := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases hb : (binSyms Li x.index : List (Fin (A + 4))) <;>
      simp [selectedSourceWords, SelectedSourceChoice.word, selectedSourceRecord, hb]

end IntegerMultBounds.MathlibTM2.Routing
