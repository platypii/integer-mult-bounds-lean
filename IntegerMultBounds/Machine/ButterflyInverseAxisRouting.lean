import IntegerMultBounds.Machine.ButterflyAxisKernel

/-! The inverse butterfly uses the same paid arithmetic followed by a physical
merge that exchanges its two role sources. The merge's finite-control role
permutation performs the exchange during the existing charged pass. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisRouting
noncomputable section
open ButterflyStreamData ButterflyAxisSerialization
open ButterflyAxisKernel (swapBit)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (groups rowLength)
variable {v : Descriptor} {N : ℕ}

def swapped {H N : ℕ} (xs : Fin H → Fin 2 → Fin N → Coefficient)
    (h : Fin H) (j : Fin 2) (k : Fin N) := xs h (swapBit j) k

def transformed {H N : ℕ} (xs : Fin H → Fin 2 → Fin N → Coefficient) :=
  swapped (ButterflyStreamSemantics.transformed xs)

theorem swapped_width (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w) :
    ∀ h j k,(swapped xs h j k).1.length=w ∧ (swapped xs h j k).2.length=w := fun h j k => hw h (swapBit j) k

theorem transformed_width (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w) :
    ∀ h j k,(transformed xs h j k).1.length=w ∧ (transformed xs h j k).2.length=w :=
  swapped_width _ w (ButterflyStreamSemantics.transformed_width xs w hw)

/-- Existing merge traversal reads the opposite physical role at each logical
bit. Source erasure and rewinds are included in exactly the same merge budget. -/
theorem merges (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) :
    HoareTime (RecursiveRowsClean.mergeProgram (by decide : 2≤2) swapBit)
      (fun z => z=RecursiveRowsClean.bank hs (ButterflyAxisRouting.rolePayload xs))
      (fun z => z=RecursiveRowsClean.bank hs (ButterflyAxisRouting.sourcePayload (swapped xs)))
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  let rs := rows (swapped xs)
  have hl : ∀ h j,(rs h j).length=rowLength 2 v :=
    fun h j => (row_length (swapped xs) w (swapped_width xs w hw) h j).trans hB.symm
  have hh := RecursiveRowsClean.merge_hoare (by decide : 2≤2) swapBit (by decide : 0<2)
    hs v hv hp hd (RecursiveRowsFromWords.array hd rs hl)
  have hm : RecursiveRowsConstruct.mergePayload swapBit hd (RecursiveRowsFromWords.array hd rs hl)
      (fun _ => blank)=ButterflyAxisRouting.rolePayload xs := by
    unfold RecursiveRowsConstruct.mergePayload RecursiveRowsConstruct.word ButterflyAxisRouting.rolePayload full
    congr 1
    funext j
    rw [RecursiveRowsFromWords.role_word]
    change putWord (fun _ => blank) 0 (CyclicRowSplit.roleWord (rows (swapped xs)) (swapBit.symm j))=_
    rw [role_word]
    simp only [paired,swapped,Equiv.apply_symm_apply]
  rw [hm,RecursiveRowsFromWords.source_payload,ButterflyAxisRouting.source_payload] at hh
  exact hh

end
end IntegerMultBounds.Machine.ButterflyInverseAxisRouting
