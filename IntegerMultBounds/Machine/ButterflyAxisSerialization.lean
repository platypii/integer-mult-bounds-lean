import IntegerMultBounds.Machine.ButterflyStreamClean
import IntegerMultBounds.Machine.RecursiveInterchangeRows

/-! Literal selected-bit serialization. Splitting the bit between the higher
and lower coordinates pairs exactly the two coefficients used by a butterfly;
all radix digits and delimiters are preserved as native symbols. -/
namespace IntegerMultBounds.Machine.ButterflyAxisSerialization
noncomputable section
open ButterflyStreamData
open RecursiveInterchangeRows (pack)
variable {H N : ℕ}

def rows (xs : Fin H → Fin 2 → Fin N → Coefficient) (h : Fin H) (j : Fin 2) :=
  (List.ofFn (fun k => encoded (xs h j k))).flatten

def paired (xs : Fin H → Fin 2 → Fin N → Coefficient) (j : Fin 2) (i : Fin (H*N)) : Coefficient :=
  let hk := finProdFinEquiv.symm i
  xs hk.1 j hk.2

def joined (xs : Fin H → Fin 2 → Fin N → Coefficient) (i : Fin (H*(2*N))) : Coefficient :=
  let hjk := finProdFinEquiv.symm i
  let jk := finProdFinEquiv.symm hjk.2
  xs hjk.1 jk.1 jk.2

private theorem serialize_mul {m n : ℕ} {α : Type*} (f : Fin (m*n) → List α) :
    (List.ofFn f).flatten=
      (List.ofFn (fun i : Fin m => (List.ofFn (fun j : Fin n => f (pack i j))).flatten)).flatten := by
  have he : List.ofFn f=(List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => f (pack i j)))).flatten := by
    simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f
  rw [he,List.flatten_flatten]
  congr 1
  simp only [List.map_ofFn,Function.comp_def]

/-- A split role contains complete coefficients in exactly (higher,lower) order. -/
theorem role_word (xs : Fin H → Fin 2 → Fin N → Coefficient) (j : Fin 2) :
    CyclicRowSplit.roleWord (rows xs) j=(List.ofFn (fun i => encoded (paired xs j i))).flatten := by
  rw [serialize_mul]
  simp only [paired,pack,Equiv.symm_apply_apply,CyclicRowSplit.roleWord,rows]

/-- The unsplit word contains (higher,selected-bit,lower) coefficient order. -/
theorem source_word (xs : Fin H → Fin 2 → Fin N → Coefficient) :
    CyclicRowSplit.sourceWord (rows xs)=(List.ofFn (fun i => encoded (joined xs i))).flatten := by
  rw [serialize_mul]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords
  congr 1
  apply congrArg List.ofFn
  funext h
  rw [serialize_mul]
  simp only [joined,pack,Equiv.symm_apply_apply]
  rfl

theorem row_length (xs : Fin H → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w) (h : Fin H) (j : Fin 2) :
    (rows xs h j).length=N*(2*(w+1)) := by
  have hh := CyclicRowSplit.prefix_length (fun k => encoded (xs h j k)) (2*(w+1))
    (fun k => DelimitedRadixRecord.complex_length _ _ _ (hw h j k).1 (hw h j k).2) N le_rfl
  rw [CyclicRowCycle.prefix_all] at hh
  exact hh

/-- The physical selected-bit split supplies the exact paired stream endpoints
consumed by the coefficient machine; no per-record permutation is assumed. -/
theorem paired_entry (xs : Fin H → Fin 2 → Fin N → Coefficient) (h : Fin H) (j : Fin 2) (k : Fin N) :
    paired xs j (pack h k)=xs h j k := by simp [paired,pack]

end
end IntegerMultBounds.Machine.ButterflyAxisSerialization
