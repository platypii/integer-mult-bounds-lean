import IntegerMultBounds.Machine.ArbitraryWidthConsumePlacement

/-! The level controller shares the slice-width tape, while its remaining six
slots live outside the slice's required blank scratch bank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthLevelPlacement
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthConsumePlacement (S T parent)
open SharedPlacementAlphabet (setTape)

def widthSlot : Fin S := Fin.natAdd ArbitrarySliceCall.rootCount (1 : Fin 12)
def source : Fin 6 → Fin 7 := ![0,1,2,3,4,6]
def extras (B j : ℕ) : Tapes 6 prime :=
  ⟨fun i => (ArbitraryWidthLevelAdvance.working (a := prime) B j).head (source i),
    fun i => (ArbitraryWidthLevelAdvance.working (a := prime) B j).tape (source i)⟩

def extraSlot (i : Fin 6) : Fin T := Fin.natAdd 14 (Fin.natAdd S i)
def widthGlobal : Fin T := Fin.natAdd 14 (Fin.castAdd 6 widthSlot)
def slot : Fin 7 → Fin T := ![extraSlot 0,extraSlot 1,extraSlot 2,extraSlot 3,
  extraSlot 4,widthGlobal,extraSlot 5]

private theorem slot_injective : Function.Injective slot := by
  intro i j he
  have hh := congrArg Fin.val he
  have hS : S = ArbitrarySliceCall.rootCount+12 := rfl
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (simp [slot,extraSlot,widthGlobal,widthSlot] at hh <;> omega)

def placement : Fin (7+(S+13)) ≃ Fin T :=
  InjectivePlacement.placement slot slot_injective (by change 7+(S+13)=14+(S+6); omega)

private theorem extra_head (B j : ℕ) (ns : List Bool) (slice : Tapes S prime) (i : Fin 6) :
    (parent ns slice (extras B j)).head (extraSlot i) =
      (ArbitraryWidthLevelAdvance.working (a := prime) B j).head (source i) := by
  simp only [parent,extraSlot,Tapes.append,Fin.addCases_right]
  rfl

private theorem extra_tape (B j : ℕ) (ns : List Bool) (slice : Tapes S prime) (i : Fin 6) :
    (parent ns slice (extras B j)).tape (extraSlot i) =
      (ArbitraryWidthLevelAdvance.working (a := prime) B j).tape (source i) := by
  simp only [parent,extraSlot,Tapes.append,Fin.addCases_right]
  rfl

private theorem width_head (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) :
    (parent ns slice level).head widthGlobal = slice.head widthSlot := by
  simp only [parent,widthGlobal,Tapes.append,Fin.addCases_right,Fin.addCases_left]

private theorem width_tape (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) :
    (parent ns slice level).tape widthGlobal = slice.tape widthSlot := by
  simp only [parent,widthGlobal,Tapes.append,Fin.addCases_right,Fin.addCases_left]

theorem active (B j : ℕ) (ns : List Bool) (slice : Tapes S prime)
    (hw : slice.tape widthSlot = RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B j))
    (hh : slice.head widthSlot = 1) :
    Placement.active placement (parent ns slice (extras B j)) = ArbitraryWidthLevelAdvance.working B j := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | exact extra_head B j ns slice 0
    | exact extra_head B j ns slice 1
    | exact extra_head B j ns slice 2
    | exact extra_head B j ns slice 3
    | exact extra_head B j ns slice 4
    | exact extra_head B j ns slice 5
    | exact (width_head ns slice (extras B j)).trans hh
    | exact extra_tape B j ns slice 0
    | exact extra_tape B j ns slice 1
    | exact extra_tape B j ns slice 2
    | exact extra_tape B j ns slice 3
    | exact extra_tape B j ns slice 4
    | exact extra_tape B j ns slice 5
    | exact (width_tape ns slice (extras B j)).trans hw

private theorem extra_eq (B j : ℕ) (ns : List Bool) (slice : Tapes S prime)
    (f : ℤ → Fin (prime+4)) :
    Placement.extra placement (parent ns slice (extras B j)) =
      Placement.extra placement (parent ns (setTape slice widthSlot f 1) (extras B (j+1))) := by
  have hf (i : Fin (S+13)) :
      let z := placement (Fin.natAdd 7 i)
      (parent ns slice (extras B j)).head z =
        (parent ns (setTape slice widthSlot f 1) (extras B (j+1))).head z ∧
      (parent ns slice (extras B j)).tape z =
        (parent ns (setTape slice widthSlot f 1) (extras B (j+1))).tape z := by
    let z := placement (Fin.natAdd 7 i)
    have hn (k : Fin 7) : z ≠ slot k := by
      rw [← InjectivePlacement.active_slot slot slot_injective
        (by change 7+(S+13)=14+(S+6); omega : 7+(S+13)=T) k]
      intro he
      have hh := congrArg Fin.val (placement.injective he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
      have := k.isLt
      omega
    change (parent ns slice (extras B j)).head z =
      (parent ns (setTape slice widthSlot f 1) (extras B (j+1))).head z ∧
      (parent ns slice (extras B j)).tape z =
      (parent ns (setTape slice widthSlot f 1) (extras B (j+1))).tape z
    generalize hz : z = w at hn ⊢
    induction w using Fin.addCases with
    | left k =>
      simp only [parent,Tapes.append,Fin.addCases_left]
      exact ⟨trivial,trivial⟩
    | right k =>
      induction k using Fin.addCases with
      | left k =>
        have hk : k ≠ widthSlot := by
          intro he
          subst k
          exact hn (5 : Fin 7) rfl
        simp only [parent,Tapes.append,Fin.addCases_right,Fin.addCases_left,
          setTape,Function.update_of_ne hk]
        exact ⟨trivial,trivial⟩
      | right k =>
        exfalso
        fin_cases k
        · exact hn (0 : Fin 7) rfl
        · exact hn (1 : Fin 7) rfl
        · exact hn (2 : Fin 7) rfl
        · exact hn (3 : Fin 7) rfl
        · exact hn (4 : Fin 7) rfl
        · exact hn (6 : Fin 7) rfl
  apply congrArg₂ Tapes.mk
  · funext i; exact (hf i).1
  · funext i; exact (hf i).2

def program := Placement.placed (ArbitraryWidthLevelAdvance.advance (a := prime)) placement

theorem advances (B j : ℕ) (hB : 2 ≤ B) (ns : List Bool) (slice : Tapes S prime)
    (hw : slice.tape widthSlot = RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B j))
    (hh : slice.head widthSlot = 1) :
    HoareTime program (fun v => v = parent ns slice (extras B j))
      (fun v => v = parent ns (setTape slice widthSlot
        (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B (j+1))) 1) (extras B (j+1)))
      (120*B^(j+1)) := by
  have h := Placement.hoare_at (ArbitraryWidthLevelAdvance.advance_linear (a := prime) B j hB)
    placement (parent ns slice (extras B j)) (active B j ns slice hw hh)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_eq]
  have ha := active B (j+1) ns (setTape slice widthSlot
    (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B (j+1))) 1) (by simp [setTape]) (by simp [setTape])
  rw [← ha]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.ArbitraryWidthLevelPlacement
