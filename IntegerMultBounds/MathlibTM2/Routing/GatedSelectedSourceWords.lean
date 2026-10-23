module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceReverse

/-! Raw source records contain local coordinates and a region tag, rather than
computed selectors. Every record is self-delimiting and has a fixed width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host

structure GatedSelectedSourceChoice where
  index : ℕ
  offset : ℕ
  lo : Bool
  hi : Bool
  enabled : Bool
  deriving DecidableEq

namespace GatedSelectedSourceChoice

def tag (x : GatedSelectedSourceChoice) : Fin 4 := sourceTagIndex x.lo x.hi

def position (x : GatedSelectedSourceChoice) (k : ℕ) (base : Fin 4 → ℕ) : ℕ :=
  x.index * k + base x.tag + x.offset

def word {A : ℕ} (x : GatedSelectedSourceChoice) (Li Lk : ℕ) : List (Fin (A + 4)) :=
  gatedSelectedSourceRecord Li Lk x.index x.offset x.lo x.hi x.enabled

theorem word_length {A : ℕ} (x : GatedSelectedSourceChoice) (Li Lk : ℕ) :
    (x.word (A := A) Li Lk).length = Li + (Li + Lk) + 5 := by
  simp [word, gatedSelectedSourceRecord]
  omega

end GatedSelectedSourceChoice

def gatedSelectedSourceWords {A : ℕ} (Li Lk : ℕ) : List GatedSelectedSourceChoice → List (Fin (A + 4))
  | [] => []
  | x :: xs => x.word Li Lk ++ gatedSelectedSourceWords Li Lk xs

theorem gatedSelectedSourceWords_length {A : ℕ} (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice) :
    (gatedSelectedSourceWords (A := A) Li Lk xs).length = xs.length * (Li + (Li + Lk) + 5) := by
  induction xs with
  | nil => simp [gatedSelectedSourceWords]
  | cons x xs ih => simp [gatedSelectedSourceWords, GatedSelectedSourceChoice.word_length, ih, Nat.add_mul]; omega

theorem gatedSelectedSourceWords_head {A : ℕ} (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice) :
    (gatedSelectedSourceWords (A := A) Li Lk xs).head?.isSome = xs.head?.isSome := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases hb : (binSyms Li x.index : List (Fin (A + 4))) <;>
      simp [gatedSelectedSourceWords, GatedSelectedSourceChoice.word, gatedSelectedSourceRecord, hb]

end IntegerMultBounds.MathlibTM2.Routing
