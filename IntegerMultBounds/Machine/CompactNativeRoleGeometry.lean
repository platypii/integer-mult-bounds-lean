import IntegerMultBounds.Machine.CompactSpectatorVisitGeometry
import IntegerMultBounds.Machine.NativeZeroPaddingArray
import IntegerMultBounds.Machine.CompactGlobalRowPadding
import IntegerMultBounds.Machine.CyclicRowSplit
import IntegerMultBounds.Machine.CompactReservationNativePaddingBudget

/-! Native coefficient row distribution keeps every immutable binary address,
polynomial coordinate and signed field. Cyclic grouping only selects outer
row c*g+j; the complete inner coordinate is unchanged. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleGeometry
noncomputable section
open RecursiveInterchangeRows (pack)
open ButterflyStreamData (Coefficient encoded)
open NativeZeroPaddingArray (word)

abbrev Array (n c L : ℕ) := Fin ((n*c)*L) → Coefficient

def role {n c L : ℕ} (f : Array n c L) (j : Fin c) : Fin (n*L) → Coefficient := fun z =>
  let ik := finProdFinEquiv.symm z
  f (pack (pack ik.1 j) ik.2)

def row {n c L : ℕ} (f : Array n c L) (i : Fin n) (j : Fin c) :=
  word (fun k : Fin L => f (pack (pack i j) k))

theorem role_index {n c L : ℕ} (f : Array n c L) (i : Fin n) (j : Fin c) (k : Fin L) :
    role f j (pack i k)=f (pack (pack i j) k) := by
  simp [role,pack]

theorem global_index {n c L : ℕ} (i : Fin n) (j : Fin c) (k : Fin L) :
    (pack (pack i j) k).val=(c*i.val+j.val)*L+k.val := by
  simp only [RecursiveInterchangeRows.pack_val]
  ring

private theorem word_group {n L : ℕ} (f : Fin (n*L) → Coefficient) :
    word f=(List.ofFn (fun i : Fin n => word (fun k : Fin L => f (pack i k)))).flatten := by
  unfold word
  have he : List.ofFn (fun z => encoded (f z))=
      (List.ofFn (fun i : Fin n => List.ofFn (fun k : Fin L => encoded (f (pack i k))))).flatten := by
    simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
      List.ofFn_mul (fun z => encoded (f z))
  rw [he,List.flatten_flatten,List.map_ofFn]
  rfl

/-- The grouped physical input is exactly the original native word; grouping
needs no preliminary copy or transpose. -/
theorem source_word {n c L : ℕ} (f : Array n c L) :
    CyclicRowSplit.sourceWord (row f)=word f := by
  rw [word_group]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords row
  have he := List.ofFn_mul (fun z : Fin (n*c) => word (fun k : Fin L => f (pack z k)))
  simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm,List.flatten_flatten,
    List.map_ofFn,Function.comp_def] using congrArg List.flatten he.symm

/-- One role retains the complete immutable inner address/polynomial stream. -/
theorem role_word {n c L : ℕ} (f : Array n c L) (j : Fin c) :
    CyclicRowSplit.roleWord (row f) j=word (role f j) := by
  rw [word_group]
  unfold CyclicRowSplit.roleWord row
  congr 2
  funext i
  congr 1
  funext k
  exact (role_index f i j k).symm

theorem row_length {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) (i : Fin n) (j : Fin c) :
    (row f i j).length=L*(2*(w+1)) := by
  unfold row
  exact CompactReservationNativePaddingBudget.word_length w _ (fun k => hw _)

end
end IntegerMultBounds.Machine.CompactNativeRoleGeometry
