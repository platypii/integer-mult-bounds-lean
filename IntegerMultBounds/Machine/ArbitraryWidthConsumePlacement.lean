import IntegerMultBounds.Machine.ArbitrarySliceRepeat
import IntegerMultBounds.Machine.ArbitraryWidthLevelAdvance
import IntegerMultBounds.Machine.ArbitraryWidthPieceLoop

/-! Concrete placement of slice repetition and level advancement in the
digit-driver bank. Runtime digit/count and width are shared physical tapes.
Level metadata occupies six separate slots outside the slice scratch bank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthConsumePlacement
noncomputable section
open Networks
open Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
abbrev S := ArbitrarySliceCall.tapeCount
abbrev T := 14+(S+6)

def parent (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) : Tapes T prime :=
  (ArbitraryWidthPieceCounter.input ns).append (slice.append level)

def emitted (ns rs : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) : Tapes T prime :=
  (ArbitraryWidthPieceCounter.ready ns rs).append (slice.append level)

def repeatSlot : Fin (S+2) → Fin T := Fin.addCases
  (fun i => Fin.natAdd 14 (Fin.castAdd 6 i))
  (fun i => Fin.castAdd (S+6) (if i = 0 then (1 : Fin 14) else 6))

private theorem repeat_injective : Function.Injective repeatSlot := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      apply congrArg (Fin.castAdd 2)
      have hh := congrArg Fin.val he
      simp only [repeatSlot,Fin.addCases_left,Fin.val_natAdd,Fin.val_castAdd] at hh
      exact Fin.ext (by omega)
    | right j =>
      have hh := congrArg Fin.val he
      fin_cases j <;> simp only [repeatSlot,Fin.addCases_left,Fin.addCases_right,Fin.val_natAdd,
        Fin.val_castAdd,Fin.zero_eta,ite_true] at hh <;> omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hh := congrArg Fin.val he
      fin_cases i <;> simp only [repeatSlot,Fin.addCases_left,Fin.addCases_right,Fin.val_natAdd,
        Fin.val_castAdd,Fin.zero_eta,ite_true] at hh <;> omega
    | right j =>
      have hh := congrArg Fin.val he
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | simp [repeatSlot] at hh

def repeatPlacement : Fin ((S+2)+18) ≃ Fin T :=
  InjectivePlacement.placement repeatSlot repeat_injective (by change (S+2)+18=14+(S+6); omega)

private theorem descriptor_binary (xs : List Bool) :
    BinaryDescriptorStack.descriptor (a := prime) xs = CountedLoopReuseAlphabet.binary xs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  change (fun z => (RadixToBinary.binaryEncoding (q := prime)).encode (CountedCopyReuse.binary xs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary xs

theorem repeat_active (ns rs : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) :
    Placement.active repeatPlacement (emitted ns rs slice level) = ArbitrarySliceRepeat.input slice rs := by
  rw [repeatPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp only [repeatSlot,Fin.addCases_left,emitted,Tapes.append,Fin.addCases_right]
  | right i =>
      fin_cases i
      all_goals simp only [repeatSlot,Fin.addCases_right,emitted,Tapes.append,Fin.addCases_left,
        CountedLoopReuseAlphabet.controls]
      all_goals first | rfl | exact descriptor_binary rs

theorem repeat_output_active (ns : List Bool) (slice : Tapes S prime) (level : Tapes 6 prime) :
    Placement.active repeatPlacement (parent ns slice level) = slice.append (SharedBank.empty 2 prime) := by
  rw [repeatPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp only [repeatSlot,Fin.addCases_left,parent,Tapes.append,Fin.addCases_right]
  | right i =>
      fin_cases i
      all_goals simp only [repeatSlot,Fin.addCases_right,parent,Tapes.append,Fin.addCases_left]
      all_goals rfl

private theorem repeat_extra (ns rs : List Bool) (slice slice' : Tapes S prime) (level : Tapes 6 prime) :
    Placement.extra repeatPlacement (emitted ns rs slice level) =
      Placement.extra repeatPlacement (parent ns slice' level) := by
  have hf (i : Fin 18) :
      let z := repeatPlacement (Fin.natAdd (S+2) i)
      (emitted ns rs slice level).head z = (parent ns slice' level).head z ∧
      (emitted ns rs slice level).tape z = (parent ns slice' level).tape z := by
    let z := repeatPlacement (Fin.natAdd (S+2) i)
    have hn (j : Fin (S+2)) : z ≠ repeatSlot j := by
      rw [← InjectivePlacement.active_slot repeatSlot repeat_injective
        (by change (S+2)+18=14+(S+6); omega : (S+2)+18=T) j]
      intro he
      have hh := congrArg Fin.val (repeatPlacement.injective he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
      have := j.isLt
      omega
    change (emitted ns rs slice level).head z = (parent ns slice' level).head z ∧
      (emitted ns rs slice level).tape z = (parent ns slice' level).tape z
    generalize hz : z = w at hn ⊢
    induction w using Fin.addCases with
    | left j =>
      have hj : j ≠ (6 : Fin 14) := by
        intro hj
        apply hn (Fin.natAdd S (1 : Fin 2))
        subst j
        simp [repeatSlot]
      simp only [emitted,parent,Tapes.append,Fin.addCases_left,
        ArbitraryWidthPieceCounter.ready,setTape,Function.update_of_ne hj]
      exact ⟨trivial,trivial⟩
    | right j =>
      induction j using Fin.addCases with
      | left j => exact (hn (Fin.castAdd 2 j) (by simp [repeatSlot])).elim
      | right j =>
        simp only [emitted,parent,Tapes.append,Fin.addCases_right]
        exact ⟨trivial,trivial⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (hf i).1
  · funext i; exact (hf i).2

theorem repeat_placed {r c : ℕ} {M : Program (S+2) r prime} (ns rs : List Bool)
    (slice slice' : Tapes S prime) (level : Tapes 6 prime)
    (h : HoareTime M (fun v => v = ArbitrarySliceRepeat.input slice rs)
      (fun v => v = slice'.append (SharedBank.empty 2 prime)) c) :
    HoareTime (Placement.placed M repeatPlacement) (fun v => v = emitted ns rs slice level)
      (fun v => v = parent ns slice' level) c := by
  apply (Placement.hoare_at h repeatPlacement (emitted ns rs slice level)
    (repeat_active ns rs slice level)).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,repeat_extra,← repeat_output_active ns slice' level]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.ArbitraryWidthConsumePlacement
