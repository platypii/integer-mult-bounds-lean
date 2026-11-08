module

public import IntegerMultBounds.MathlibTM2.Routing.HaloWindowPair

/-! Structural data and amortization for monotone window pairs. A retained tail
is read from the source once and reused as the next window's old overlap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloScanLayout
open IntegerMultBounds.MathlibTM2.Host

structure WindowPair (β : Type) where
  fresh₁ : List β
  kept₁ : List β
  fresh₂ : List β
  kept₂ : List β

namespace WindowPair
variable {β : Type}

def input (x : WindowPair β) : List β := x.fresh₁++x.kept₁++x.fresh₂++x.kept₂

def output (old : List β) (x : WindowPair β) : List β :=
  (old++x.fresh₁++x.kept₁)++(x.kept₁++x.fresh₂++x.kept₂)

def Fits (V : ℕ) (x : WindowPair β) : Prop :=
  x.fresh₁.length < 2^V ∧ x.kept₁.length < 2^V ∧ x.fresh₂.length < 2^V ∧ x.kept₂.length < 2^V

def metadata {A : ℕ} (V : ℕ) (x : WindowPair (Fin (A+4))) : List (Fin (A+4)) :=
  binSyms V x.fresh₁.length++binSyms V x.kept₁.length++binSyms V x.fresh₂.length++binSyms V x.kept₂.length

end WindowPair
variable {β : Type}

def output : List β → List (WindowPair β) → List β
  | _, [] => []
  | old, x::xs => x.output old++output x.kept₂ xs

def remainingOverlap : List β → List (WindowPair β) → List β
  | old, [] => old
  | _, x::xs => remainingOverlap x.kept₂ xs

/-- Loop cost includes pop, peek and loop transition, with one final test. -/
def loopCost (V : ℕ) : List β → List (WindowPair β) → ℕ
  | _, [] => 1
  | old, x::xs => 2*old.length+18*(x.fresh₁.length+x.fresh₂.length)+30*x.kept₁.length+
      28*x.kept₂.length+76*V+149+loopCost V x.kept₂ xs

theorem loopCost_le (V : ℕ) (old : List β) (xs : List (WindowPair β)) :
    loopCost V old xs ≤ 2*old.length+30*(xs.flatMap WindowPair.input).length+xs.length*(76*V+149)+1 := by
  induction xs generalizing old with
  | nil => simp [loopCost]
  | cons x xs ih =>
    have h := ih x.kept₂
    simp only [loopCost,List.flatMap_cons,List.length_append,WindowPair.input,List.length_cons,Nat.succ_mul] at *
    omega

theorem output_length_le (old : List β) (xs : List (WindowPair β)) :
    (output old xs).length+(remainingOverlap old xs).length ≤ old.length+2*(xs.flatMap WindowPair.input).length := by
  induction xs generalizing old with
  | nil => simp [output,remainingOverlap]
  | cons x xs ih =>
    have h := ih x.kept₂
    simp only [output,remainingOverlap,WindowPair.output,WindowPair.input,List.flatMap_cons,List.length_append] at *
    omega

end IntegerMultBounds.MathlibTM2.Routing.HaloScanLayout
