module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadColumn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadPrepare

/-! Shared register layout for loading and executing either sign of a pivot column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host

namespace HeadPivotLayout
def shear : Fin 29 ↪ Fin 53 := Fin.castLEEmb (by decide)
def child : Fin 20 ↪ Fin 53 :=
  ⟨fun j => ⟨29+j.val,by omega⟩,fun _ _ eq => Fin.ext (by have := congrArg Fin.val eq; dsimp at this; omega)⟩
def reader (odd : Bool) : Fin 7 ↪ Fin 53 :=
  ⟨![30,51,if odd then 50 else 49,52,31,32,34],by cases odd <;> decide⟩
def coeff (negative : Bool) : Fin 17 ↪ Fin 53 :=
  ⟨![30,31,33,32,34,35,36,37,38,39,40,42,46,52,if negative then 41 else 29,0,48],
    by cases negative <;> decide⟩

theorem child_apart (odd : Bool) : ∀ j, child j ≠ reader odd 3 := by cases odd <;> decide
theorem shared (negative : Bool) : coeff negative 15 = shear 0 := by cases negative <;> rfl
theorem apart (negative : Bool) : ∀ j, j ≠ 15 → ∀ b, shear b ≠ coeff negative j := by cases negative <;> decide

/-- The prepared configuration already meets the column contract. The new stage
sits on its own tape and both signs of the reciprocal remain available. -/
theorem ready_after_prepare {T A M d W : ℕ} [NeZero M] {α : Type}
    (host : Fin 53 ↪ Fin T) (odd negative : Bool) (H J : ℕ)
    (S D : Stacks T A) (matrix parent : List (Fin (A+4))) (inv : ZMod M)
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α) :
    let r := (reader odd).trans host
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    HeadColumnReady h s H J [] parent [] sym source dest p q word S →
    D.R (r 3) = matrix ++ S.R (r 3) →
    D.R (c 0) = binSyms H inv.val → D.R (c 12) = binSyms H (-inv).val →
    D.L = S.L →
    (∀ j, j ≠ r 3 → j ≠ c 0 → j ≠ c 14 → j ≠ c 12 → D.R j = S.R j) →
    HeadColumnReady h s H J matrix parent (binSyms H (if negative then -inv else inv).val)
      sym source dest p q word D := by
  intro r c h s initial loaded pos neg left frame
  have safe (j : Fin 53) (hj : j ≠ reader odd 3 ∧ j ≠ child 0 ∧ j ≠ child 14 ∧ j ≠ child 12) :
      D.R (host j) = S.R (host j) :=
    frame _ (host.injective.ne hj.1) (host.injective.ne hj.2.1) (host.injective.ne hj.2.2.1) (host.injective.ne hj.2.2.2)
  have bankSafe (j : Fin 29) : D.R (s j) = S.R (s j) :=
    safe _ ((by cases odd <;> decide : ∀ b, shear b ≠ reader odd 3 ∧ shear b ≠ child 0 ∧
      shear b ≠ child 14 ∧ shear b ≠ child 12) j)
  have coeffSafe (j : Fin 17) (hj : j ≤ 11 ∨ j = 16) : D.R (h j) = S.R (h j) :=
    safe _ ((by cases odd <;> cases negative <;> decide : ∀ b : Fin 17, b ≤ 11 ∨ b = 16 →
      coeff negative b ≠ reader odd 3 ∧ coeff negative b ≠ child 0 ∧
      coeff negative b ≠ child 14 ∧ coeff negative b ≠ child 12) j hj)
  have same : h 13 = r 3 := congrArg host (by cases odd <;> cases negative <;> rfl)
  rw [← same,initial.stage,List.append_nil] at loaded
  refine ⟨loaded,(coeffSafe 16 (by decide)).trans initial.weights,?_,
    (coeffSafe 2 (by decide)).trans initial.modulus,
    fun j hj => (coeffSafe j (by omega)).trans (initial.coeffWork j hj),
    (bankSafe 2).trans initial.base,(bankSafe 28).trans initial.one,(bankSafe 27).trans initial.width,
    fun j hj => ⟨left ▸ (initial.scratch j hj).1,(bankSafe j).trans (initial.scratch j hj).2⟩,?_,?_⟩
  · cases negative
    · exact pos
    · exact neg
  · simpa only [left,bankSafe] using initial.src
  · simpa only [left,bankSafe] using initial.dst

/-- Clearing the four preparation outputs preserves the permuted payload and
returns the stage and reciprocal inputs to their empty entry state. -/
theorem ready_after_clear {T A M d W : ℕ} [NeZero M] {α : Type}
    (host : Fin 53 ↪ Fin T) (negative : Bool) (H J : ℕ) (S : Stacks T A)
    (matrix parent pivot : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α) :
    let h := (coeff negative).trans host
    let s := shear.trans host
    let outputs := [host 52,host (child 0),host (child 12),host (child 14)]
    HeadColumnReady h s H J matrix parent pivot sym source dest p q word S →
    HeadColumnReady h s H J [] parent [] sym source dest p q word
      {S with R := fun j => if j ∈ outputs then [] else S.R j} := by
  intro h s outputs ready
  let D : Stacks T A := {S with R := fun j => if j ∈ outputs then [] else S.R j}
  have keep (j : Fin 53) (hj : j ∉ [52,child 0,child 12,child 14]) : D.R (host j) = S.R (host j) := by
    have ne : host j ∉ outputs := by simpa only [outputs,List.mem_cons,List.not_mem_nil,or_false,host.injective.eq_iff] using hj
    simp [D,ne]
  have bankKeep (j : Fin 29) : D.R (s j) = S.R (s j) :=
    keep _ ((by decide : ∀ b, shear b ∉ [52,child 0,child 12,child 14]) j)
  have coeffKeep (j : Fin 17) (hj : j ≤ 11 ∨ j = 16) : D.R (h j) = S.R (h j) :=
    keep _ ((by cases negative <;> decide : ∀ b : Fin 17, b ≤ 11 ∨ b = 16 →
      coeff negative b ∉ [52,child 0,child 12,child 14]) j hj)
  change HeadColumnReady _ _ _ _ _ _ _ _ _ _ _ _ _ D
  refine ⟨?_,(coeffKeep 16 (by decide)).trans ready.weights,?_,(coeffKeep 2 (by decide)).trans ready.modulus,
    fun j hj => (coeffKeep j (by omega)).trans (ready.coeffWork j hj),
    (bankKeep 2).trans ready.base,(bankKeep 28).trans ready.one,(bankKeep 27).trans ready.width,
    fun j hj => ⟨(ready.scratch j hj).1,(bankKeep j).trans (ready.scratch j hj).2⟩,?_,?_⟩
  · have mem : h 13 ∈ outputs := List.mem_cons_self
    simp [D,mem]
  · have mem : h 14 ∈ outputs := by
      cases negative <;> simp [h,outputs,coeff,child] <;> decide
    simp [D,mem]
  · simpa only [bankKeep] using ready.src
  · simpa only [bankKeep] using ready.dst

end HeadPivotLayout
end IntegerMultBounds.MathlibTM2.Cover.Fallback
