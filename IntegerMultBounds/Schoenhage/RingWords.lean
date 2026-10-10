import IntegerMultBounds.Schoenhage.RingMath
import IntegerMultBounds.Schoenhage.Lists

/-! Signed coefficient words. A coefficient is a two's complement word, least
significant bit first (`sv`). Flipping its top bit gives the offset digit
`sv t + 2^(|t| - 1)` (`bval_flipLast`), and a streaming rule does the flip in
one pass (`Rules.output_flip`). The output word of a coefficient is its value
modulo `2^w` (`tw`), and truncation toward zero is `trunc0`. -/

namespace IntegerMultBounds.Schoenhage

open Strm

/-- The signed value of a two's complement word. -/
def sv (t : List Bool) : ℤ :=
  (bval t.dropLast : ℤ) - if t.getLastD false then 2 ^ (t.length - 1) else 0

/-- The word with its last bit flipped. -/
def flipLast (t : List Bool) : List Bool := t.dropLast ++ [!(t.getLastD false)]

theorem length_flipLast {t : List Bool} (h : t ≠ []) : (flipLast t).length = t.length := by
  have := List.length_pos_of_ne_nil h
  simp [flipLast]; omega

theorem bval_flipLast {t : List Bool} (h : t ≠ []) :
    (bval (flipLast t) : ℤ) = sv t + 2 ^ (t.length - 1) := by
  unfold flipLast sv
  rw [bval_append, List.length_dropLast]
  cases t.getLastD false <;> simp

/-- The `w`-bit word of an integer modulo `2^w`. -/
def tw (w : ℕ) (z : ℤ) : List Bool := bits w (z % 2 ^ w).toNat

/-- Truncation toward zero of `h / 2^s`. -/
def trunc0 (s : ℕ) (h : ℤ) : ℤ := if 0 ≤ h then h / 2 ^ s else -((-h) / 2 ^ s)

namespace Rules

/-- Copy the driver, flipping its last bit: each bit is held back one step. -/
abbrev flip : Rule 0 where
  Q := Option Bool
  q0 := none
  step q b _ := (some b, q.map some, fun _ => false)
  flush q := match q with
    | some c => [some (!c), none]
    | none => [none]
  B := 2
  hB q := by cases q <;> simp

theorem go_flip (c : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    (go flip (some c) w ws).2.1 = (c :: w).dropLast.map some ∧
      (go flip (some c) w ws).1 = some ((c :: w).getLastD false) := by
  induction w generalizing c ws with
  | nil => simp [go]
  | cons b w ih =>
    obtain ⟨h1, h2⟩ := ih b (fun j => if false = true then (ws j).tail else ws j)
    simp only [go]
    refine ⟨?_, ?_⟩
    · simp only [Option.map_some, Option.toList_some, List.singleton_append] at h1 ⊢
      rw [h1]
      simp [List.dropLast_cons_of_ne_nil]
    · rw [h2]; simp [List.getLastD_cons]

theorem output_flip (t : List Bool) (ws : Fin 0 → List Bool) (h : t ≠ []) :
    output flip t ws = syms [flipLast t] := by
  obtain ⟨b, w, rfl⟩ : ∃ b w, t = b :: w := by
    cases t with
    | nil => exact absurd rfl h
    | cons b w => exact ⟨b, w, rfl⟩
  unfold output
  simp only [go, Option.map_none, Option.toList_none, List.nil_append]
  obtain ⟨h1, h2⟩ := go_flip b w (fun j => if false = true then (ws j).tail else ws j)
  rw [h1, h2]
  simp [syms_cons, flipLast]

end Rules

end IntegerMultBounds.Schoenhage
