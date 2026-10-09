import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! Canonical optional-header banks for the finite synthesis schedule. An
absent entry is physically blank at zero, never a supplied derived word. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersWords
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

abbrev Words := Fin 25 → Option (List Bool)
def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
def tape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs
def common (xs : Words) : Tapes 25 a := ⟨fun i => head (xs i),fun i => tape (xs i)⟩
def bank (xs : Words) := CompactGadgetReservationHeadersCore.bank (common (a := a) xs)
def word (xs : Words) (i : Fin 25) := (xs i).getD []
def value (xs : Words) (i : Fin 25) := Counter.value (word xs i)
def Source (xs : Words) (i : Fin 25) : Prop :=
  xs i = some (word xs i) ∧ GrowingCounterData.Canonical (word xs i)
def install (xs : Words) (i : Fin 25) (N : ℕ) : Words := Function.update xs i (some (bits N))

theorem installs (xs : Words) (i : Fin 25) (N : ℕ) :
    common (a := a) (install xs i N) =
      setTape (common xs) i (RadixZeroFill.encodedBinary (bits N)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j = i
  all_goals first
    | (subst j; simp [common,install,head,tape])
    | simp only [common,install,Function.update_of_ne hj]

theorem erases (xs : Words) (i : Fin 25) :
    common (a := a) (Function.update xs i none) =
      setTape (common xs) i (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j = i
  all_goals first
    | (subst j; simp [common,head,tape])
    | simp only [common,Function.update_of_ne hj]

theorem source_head (xs : Words) (i : Fin 25) (hs : Source xs i) :
    (common (a := a) xs).head i = 1 := by simp only [common,hs.1,head]
theorem source_tape (xs : Words) (i : Fin 25) (hs : Source xs i) :
    (common (a := a) xs).tape i = RadixZeroFill.encodedBinary (word xs i) := by
  simp only [common,hs.1,tape]
theorem absent_head (xs : Words) (i : Fin 25) (hs : xs i = none) :
    (common (a := a) xs).head i = 0 := by simp only [common,hs,head]
theorem absent_tape (xs : Words) (i : Fin 25) (hs : xs i = none) :
    (common (a := a) xs).tape i = fun _ => blank := by simp only [common,hs,tape]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersWords
