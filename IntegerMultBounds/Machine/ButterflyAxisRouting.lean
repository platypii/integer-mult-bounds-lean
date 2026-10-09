import IntegerMultBounds.Machine.ButterflyStreamSemantics
import IntegerMultBounds.Machine.RecursiveRowsFromWords

/-! Clean selected-bit splitting and inverse merging of actual delimited
complex coefficients. The generic row array is constructed from literal input
words, so the endpoints have no caller-provided codec or per-record oracle. -/
namespace IntegerMultBounds.Machine.ButterflyAxisRouting
noncomputable section
open ButterflyStreamData ButterflyAxisSerialization
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (groups rowLength)
variable {v : Descriptor} {N : ℕ}

def sourcePayload (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) : Tapes 3 2 :=
  CyclicRowCopy.payload (c:=2) (full (fun _ => blank) 0 (joined xs)) (fun _ _ => blank) 0 (fun _ => 0)

def rolePayload (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) : Tapes 3 2 :=
  CyclicRowCopy.payload (fun _ => blank) (fun j => full (fun _ => blank) 0 (paired xs j)) 0 (fun _ => 0)

theorem source_payload (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) :
    RecursiveRowsFromWords.sourcePayload (rows xs)=sourcePayload xs := by
  simp only [RecursiveRowsFromWords.sourcePayload,sourcePayload,full,source_word]

theorem role_payload (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) :
    RecursiveRowsFromWords.rolePayload (rows xs)=rolePayload xs := by
  simp only [RecursiveRowsFromWords.rolePayload,rolePayload,full,role_word]

/-- The selected address bit is the two-role cyclic coordinate. Each physical
role contains the matching (higher,lower) coefficient stream at head zero; the
old common source and all generated work are physically blank. -/
theorem splits (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) :
    HoareTime (RecursiveRowsClean.splitProgram (by decide : 2≤2) (c:=2))
      (fun z => z=RecursiveRowsClean.bank hs (sourcePayload xs))
      (fun z => z=RecursiveRowsClean.bank hs (rolePayload xs))
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  have hh := RecursiveRowsFromWords.splits (by decide : 2≤2) (by decide : 0<2) hs hv hp hd
    (rows xs) (fun h j => (row_length xs w hw h j).trans hB.symm)
  rw [source_payload,role_payload] at hh
  exact hh

/-- The same literal record boundary is used after the paired arithmetic scan.
The merge restores the unique common stream and erases both role streams. -/
theorem merges (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) :
    HoareTime (RecursiveRowsClean.mergeProgram (by decide : 2≤2) (Equiv.refl (Fin 2)))
      (fun z => z=RecursiveRowsClean.bank hs (rolePayload xs))
      (fun z => z=RecursiveRowsClean.bank hs (sourcePayload xs))
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  have hh := RecursiveRowsFromWords.merges (by decide : 2≤2) (by decide : 0<2) hs hv hp hd
    (rows xs) (fun h j => (row_length xs w hw h j).trans hB.symm)
  rw [source_payload,role_payload] at hh
  exact hh

/-- Literal pairing does not omit or add any coefficient cells. The routing and
arithmetic volume budgets are therefore exactly the same serialized quantity. -/
theorem volume_eq (hd : 2 ∣ v.rows) (w : ℕ) (hB : rowLength 2 v=N*(2*(w+1))) :
    volume 2 v=4*(groups 2 v*N)*(w+1) := by
  rw [RecursiveInterchangeRows.volume_split 2 2 v hd,hB]
  ring

theorem transformed_merges (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) :
    HoareTime (RecursiveRowsClean.mergeProgram (by decide : 2≤2) (Equiv.refl (Fin 2)))
      (fun z => z=RecursiveRowsClean.bank hs (rolePayload (ButterflyStreamSemantics.transformed xs)))
      (fun z => z=RecursiveRowsClean.bank hs (sourcePayload (ButterflyStreamSemantics.transformed xs)))
      (RecursiveRowsClean.bound 2 (volume 2 v)) :=
  merges hs hv hp hd _ w (ButterflyStreamSemantics.transformed_width xs w hw) hB

end
end IntegerMultBounds.Machine.ButterflyAxisRouting
