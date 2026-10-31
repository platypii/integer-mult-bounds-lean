module

public import IntegerMultBounds.Machine.LevelLoop
public import IntegerMultBounds.Machine.SharedBankStageInput
public import IntegerMultBounds.Machine.InjectivePlacement
public import IntegerMultBounds.Machine.PlacementBank
public import IntegerMultBounds.Machine.CounterAdvance

/-!
# Padding level loops

A level loop on a common bank padded to `T₁` blank tapes runs on the same bank padded to any
`T₂ ≥ T₁`: the loop's tapes go to the first `T₁` tapes and its two controls to the last two
(`pad_hoare`). So the level loops of a segment's atom operations, each on its own number of tapes,
run in order on one common bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad

open IntegerMultBounds.Machine
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
variable {a k : ℕ}
noncomputable section

theorem loop_head (x : Tapes k a) (T f : ℕ) (hk : k ≤ T) (i : Fin (T+2)) :
    (LevelLoop.bank (raw x T) f).head i = if h : i.val < k then x.head ⟨i.val, h⟩ else if i.val < T then 0 else 1 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [LevelLoop.bank, CountedLoopReuseAlphabet.bank, Tapes.append, raw]
  · have h1 : ¬ T + j.val < k := by omega
    fin_cases j <;> simp [LevelLoop.bank, CountedLoopReuseAlphabet.bank, CountedLoopReuseAlphabet.controls,
      Tapes.append, h1]
    all_goals intro h; omega

theorem loop_tape (x : Tapes k a) (T f : ℕ) (hk : k ≤ T) (i : Fin (T+2)) :
    (LevelLoop.bank (raw x T) f).tape i = if h : i.val < k then x.tape ⟨i.val, h⟩ else if i.val < T then
      (fun _ => blank) else if i.val = T then CountedLoopReuseAlphabet.empty else
      CountedLoopReuseAlphabet.binary (bits (f-1)) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [LevelLoop.bank, CountedLoopReuseAlphabet.bank, Tapes.append, raw]
  · have h1 : ¬ T + j.val < k := by omega
    fin_cases j <;> simp [LevelLoop.bank, CountedLoopReuseAlphabet.bank, CountedLoopReuseAlphabet.controls,
      Tapes.append, h1]
    all_goals intro h; omega

/-- The slots of a padded loop: its tapes first, its controls last. -/
def pad (T₁ T₂ : ℕ) (h : T₁ ≤ T₂) (i : Fin (T₁+2)) : Fin (T₂+2) :=
  if i.val < T₁ then ⟨i.val, by omega⟩ else ⟨i.val + (T₂ - T₁), by omega⟩

theorem pad_val (T₁ T₂ : ℕ) (h : T₁ ≤ T₂) (i : Fin (T₁+2)) :
    (pad T₁ T₂ h i).val = if i.val < T₁ then i.val else i.val + (T₂ - T₁) := by
  unfold pad; split <;> rfl

theorem pad_injective (T₁ T₂ : ℕ) (h : T₁ ≤ T₂) : Function.Injective (pad T₁ T₂ h) := by
  intro i j he
  have := congrArg Fin.val he
  rw [pad_val, pad_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

/-- The placement of a padded loop. -/
def placement (T₁ T₂ : ℕ) (h : T₁ ≤ T₂) :=
  InjectivePlacement.placement (pad T₁ T₂ h) (pad_injective T₁ T₂ h) (show T₁+2 + (T₂+2 - (T₁+2)) = T₂+2 by omega)

/-- The active bank of a padded loop is the original smaller loop bank. -/
theorem active_loop_bank {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) (hk : k ≤ T₁)
    (x : Tapes k a) (f : ℕ) :
    Placement.active (placement T₁ T₂ h) (LevelLoop.bank (raw x T₂) f) =
      LevelLoop.bank (raw x T₁) f := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  refine Placement.Tapes.ext' (fun i => ?_) (fun i => ?_) <;> dsimp only
  · rw [loop_head x T₂ f (by omega), loop_head x T₁ f hk, pad_val]
    split_ifs <;> first | rfl | omega
  · rw [loop_tape x T₂ f (by omega), loop_tape x T₁ f hk, pad_val]
    split_ifs <;> first | rfl | omega

/-- **A padded loop.** -/
theorem pad_hoare {T₁ T₂ q c : ℕ} (h : T₁ ≤ T₂) (hk : k ≤ T₁) (M : Program (T₁+2) q a) (x y : Tapes k a)
    (f : ℕ) (hM : HoareTime M (fun z => z = LevelLoop.bank (raw x T₁) f)
      (fun z => z = LevelLoop.bank (raw y T₁) f) c) :
    HoareTime (Placement.placed M (placement T₁ T₂ h)) (fun z => z = LevelLoop.bank (raw x T₂) f)
      (fun z => z = LevelLoop.bank (raw y T₂) f) c := by
  refine InjectivePlacement.hoare_exact (X := LevelLoop.bank (raw x T₁) f) (X' := LevelLoop.bank (raw y T₁) f)
    hM _ _ _ _ _ ?_ ?_
  · exact active_loop_bank h hk x f
  · apply CounterAdvance.replace_eq
    · intro i
      rw [loop_head y T₂ f (by omega), loop_head y T₁ f hk, loop_tape y T₂ f (by omega),
        loop_tape y T₁ f hk, pad_val]
      constructor <;> split_ifs <;> first | rfl | omega
    · intro j hj
      have hj2 := j.isLt
      have hlo : T₁ ≤ j.val := by
        by_contra hlt
        exact hj ⟨j.val, by omega⟩ (Fin.ext (by rw [pad_val]; simp; omega))
      have hhi : j.val < T₂ := by
        by_contra hge
        exact hj ⟨j.val - (T₂ - T₁), by omega⟩ (Fin.ext (by rw [pad_val]; split_ifs <;> simp at * <;> omega))
      rw [loop_head y T₂ f (by omega), loop_head x T₂ f (by omega), loop_tape y T₂ f (by omega),
        loop_tape x T₂ f (by omega)]
      have h1 : ¬ j.val < k := by omega
      simp [h1, hhi]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad
