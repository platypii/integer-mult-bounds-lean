import IntegerMultBounds.Machine.ArbitraryWidthPieceConsume

/-! Physical initialization and erasure of the shared width/depth controller. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthLevelLifecycle
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthConsumePlacement (S T parent)
open ArbitraryWidthLevelPlacement (placement slot widthSlot extras)
open SharedPlacementAlphabet (setTape)

private theorem slot_injective : Function.Injective slot := by
  intro i j he
  have hh := congrArg Fin.val he
  have hS : S = ArbitrarySliceCall.rootCount+12 := rfl
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (simp [slot,ArbitraryWidthLevelPlacement.extraSlot,
    ArbitraryWidthLevelPlacement.widthGlobal,widthSlot] at hh <;> omega)

theorem extra_eq (ns : List Bool) (slice : Tapes S prime)
    (level level' : Tapes 6 prime) (f : ℤ → Fin (prime+4)) (p : ℤ) :
    Placement.extra placement (parent ns slice level) =
      Placement.extra placement (parent ns (setTape slice widthSlot f p) level') := by
  have hf (i : Fin (S+13)) :
      let z := placement (Fin.natAdd 7 i)
      (parent ns slice level).head z =
        (parent ns (setTape slice widthSlot f p) level').head z ∧
      (parent ns slice level).tape z =
        (parent ns (setTape slice widthSlot f p) level').tape z := by
    let z := placement (Fin.natAdd 7 i)
    have hn (k : Fin 7) : z ≠ slot k := by
      rw [← InjectivePlacement.active_slot slot slot_injective
        (by change 7+(S+13)=14+(S+6); omega : 7+(S+13)=T) k]
      intro he
      have hh := congrArg Fin.val (placement.injective he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
      have := k.isLt
      omega
    change (parent ns slice level).head z =
      (parent ns (setTape slice widthSlot f p) level').head z ∧
      (parent ns slice level).tape z =
      (parent ns (setTape slice widthSlot f p) level').tape z
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

private theorem empty_head (ns : List Bool) (slice : Tapes S prime) (i : Fin 6) :
    (parent ns slice (SharedBank.empty 6 prime)).head (ArbitraryWidthLevelPlacement.extraSlot i) = 0 := by
  simp only [parent,ArbitraryWidthLevelPlacement.extraSlot,Tapes.append,Fin.addCases_right]
  rfl
private theorem empty_tape (ns : List Bool) (slice : Tapes S prime) (i : Fin 6) :
    (parent ns slice (SharedBank.empty 6 prime)).tape (ArbitraryWidthLevelPlacement.extraSlot i) = fun _ => blank := by
  simp only [parent,ArbitraryWidthLevelPlacement.extraSlot,Tapes.append,Fin.addCases_right]
  rfl
private theorem width_head (ns : List Bool) (slice : Tapes S prime) :
    (parent ns slice (SharedBank.empty 6 prime)).head ArbitraryWidthLevelPlacement.widthGlobal = slice.head widthSlot := by
  simp only [parent,ArbitraryWidthLevelPlacement.widthGlobal,Tapes.append,Fin.addCases_right,Fin.addCases_left]
private theorem width_tape (ns : List Bool) (slice : Tapes S prime) :
    (parent ns slice (SharedBank.empty 6 prime)).tape ArbitraryWidthLevelPlacement.widthGlobal = slice.tape widthSlot := by
  simp only [parent,ArbitraryWidthLevelPlacement.widthGlobal,Tapes.append,Fin.addCases_right,Fin.addCases_left]

theorem active_empty (ns : List Bool) (slice : Tapes S prime)
    (ht : slice.tape widthSlot = fun _ => blank) (hh : slice.head widthSlot = 0) :
    Placement.active placement (parent ns slice (SharedBank.empty 6 prime)) = SharedBank.empty 7 prime := by
  rw [ArbitraryWidthLevelPlacement.placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | exact empty_head ns slice 0
    | exact empty_head ns slice 1
    | exact empty_head ns slice 2
    | exact empty_head ns slice 3
    | exact empty_head ns slice 4
    | exact empty_head ns slice 5
    | exact (width_head ns slice).trans hh
    | exact empty_tape ns slice 0
    | exact empty_tape ns slice 1
    | exact empty_tape ns slice 2
    | exact empty_tape ns slice 3
    | exact empty_tape ns slice 4
    | exact empty_tape ns slice 5
    | exact (width_tape ns slice).trans ht

def setup (B : ℕ) := Placement.placed (ArbitraryWidthLevelAdvance.setup (a := prime) B) placement
def finish := Placement.placed (ArbitraryWidthLevelAdvance.finish (a := prime)) placement

theorem initializes (B : ℕ) (ns : List Bool) (slice : Tapes S prime)
    (ht : slice.tape widthSlot = fun _ => blank) (hh : slice.head widthSlot = 0) :
    HoareTime (setup B) (fun z => z = parent ns slice (SharedBank.empty 6 prime))
      (fun z => z = parent ns (setTape slice widthSlot
        (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B 0)) 1) (extras B 0))
      (RecursiveChildQuotientsConstant.cost B+RecursiveChildQuotientsConstant.cost 1+
        RecursiveChildQuotientsConstant.cost 0+2) := by
  have h := Placement.hoare_at (ArbitraryWidthLevelAdvance.setup_hoare (a := prime) B)
    placement (parent ns slice (SharedBank.empty 6 prime)) (active_empty ns slice ht hh)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_eq]
  have ha := ArbitraryWidthLevelPlacement.active B 0 ns (setTape slice widthSlot
    (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B 0)) 1) (by simp [setTape]) (by simp [setTape])
  rw [← ha]
  exact Placement.view _ _

theorem cleans (B j : ℕ) (hB : 2 ≤ B) (ns : List Bool) (slice : Tapes S prime)
    (ht : slice.tape widthSlot = RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B j))
    (hh : slice.head widthSlot = 1) :
    HoareTime finish (fun z => z = parent ns slice (extras B j))
      (fun z => z = parent ns (setTape slice widthSlot (fun _ => blank) 0) (SharedBank.empty 6 prime))
      ((2*(RecursiveChildQuotientsConstant.bits B).length+20)*B^j) := by
  have h := Placement.hoare_at (ArbitraryWidthLevelAdvance.finish_linear (a := prime) B j hB)
    placement (parent ns slice (extras B j)) (ArbitraryWidthLevelPlacement.active B j ns slice ht hh)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_eq]
  have ha := active_empty ns (setTape slice widthSlot (fun _ => blank) 0)
    (by simp [setTape]) (by simp [setTape])
  rw [← ha]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.ArbitraryWidthLevelLifecycle
