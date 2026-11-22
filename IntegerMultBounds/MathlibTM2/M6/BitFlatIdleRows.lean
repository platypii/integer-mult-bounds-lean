module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall

/-! Supply internal remainder calls with the cyclic owner rows of their parent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

/-- Dividing the inherited row stock between the owners preserves the precise
offsets used by the cyclic splitter and merger, including the parent's spectators. -/
theorem IdleChildPositions.internalRows_iff {child : Descriptor} (parent : Descriptor)
    (i : Fin 9) (j : Fin 222) (w rows : ℕ) (stock : 142080 ∣ rows) :
    let tail := fun r => parent.beforeRows*r*parent.beforeH*parent.between*parent.afterD
    let W := tail rows
    let e := idleInterval i j
    let lane := phaseIntervalChild e.1 e.2 w (tail (rows/142080)) 64
    ∀ (position : Fin (volume prime child) ≃ Fin ((prime^w)^128*W)),
      IdleChildPositions i j w W child position →
      ∃ span : volume prime lane * 142080 = (prime^w)^128*W,
        ∀ {α : Type} (word changed : Fin ((prime^w)^128*W) → α),
          let offset := fun (a : Fin (volume prime lane)) (r : Fin 142080) => (finProdFinEquiv (a,r)).cast span
          (∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k) ↔
            ∀ a r, changed (offset a r) = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows)
              (fun k => word (offset k r)) a := by
  intro tail W e lane position coords
  have split : W = tail (rows/142080)*142080 := by
    dsimp only [W,tail]
    conv_lhs => rw [← Nat.div_mul_cancel stock]
    ac_rfl
  have bounds := idleBounds i j
  have span : volume prime lane*142080 = (prime^w)^128*W := by
    rw [split,← Nat.mul_assoc]
    exact congrArg (·*142080) (intervalChild_volume bounds.1 (bounds.2.trans (by decide : 63 ≤ 64)) w _)
  refine ⟨span,?_⟩
  intro α word changed
  apply InheritedIntervalPositions.trailingRows_iff coords.2 coords.1
  dsimp only [lane]
  simp [e,split,phaseIntervalChild,Nat.mul_assoc]

end IntegerMultBounds.MathlibTM2.M6.BitNode
