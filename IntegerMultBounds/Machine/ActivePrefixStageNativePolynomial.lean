import IntegerMultBounds.Machine.ActivePrefixStageNativePairSchedule
import IntegerMultBounds.Machine.UnitPhaseFullStreamNormalized

/-! Canonical native rows are literal serialized polynomial coefficients.
A basis stage changes the original address row while retaining every polynomial
coefficient and stored digit. No polynomial count is inferred from word width. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ButterflyStreamData (Coefficient encoded)
open UnitPhaseFullStreamNormalized (serialized)
variable {s : Shape} {N R w : ℕ}

def symbols (R w : ℕ) := 2*(w+1)*R

def flattenArray {X : Type*} {N R : ℕ} (xs : Fin N → Fin R → X) (k : Fin (N*R)) : X :=
  let rj := finProdFinEquiv.symm k
  xs rj.1 rj.2

theorem ofFn_flattenArray {X : Type*} {N R : ℕ} (xs : Fin N → Fin R → X) :
    List.ofFn (flattenArray xs)=(List.ofFn (fun i => List.ofFn (xs i))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hj : (⟨i.val*R+j.val,by
    have hm := Nat.mul_le_mul_right R (Nat.succ_le_of_lt i.isLt)
    nlinarith [j.isLt]⟩ : Fin (N*R))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hj]
  simp only [flattenArray,Equiv.symm_apply_apply]

theorem row_length (xs : Fin R → Coefficient)
    (hw : ∀ j,(xs j).1.length=w ∧ (xs j).2.length=w) :
    (serialized xs).length=symbols R w := by
  have h := CyclicRowSplit.prefix_length (fun j => encoded (xs j)) (2*(w+1))
    (fun j => DelimitedRadixRecord.complex_length _ _ _ (hw j).1 (hw j).2) R le_rfl
  rw [CyclicRowCycle.prefix_all] at h
  simpa only [serialized,symbols,Nat.mul_comm] using h

def row (xs : Fin R → Coefficient) (hw : ∀ j,(xs j).1.length=w ∧ (xs j).2.length=w) :
    Fin (symbols R w) → Fin 6 :=
  fun k => (serialized xs).get (Fin.cast (row_length xs hw).symm k)

theorem row_word (xs : Fin R → Coefficient) (hw : ∀ j,(xs j).1.length=w ∧ (xs j).2.length=w) :
    List.ofFn (row xs hw)=serialized xs := by
  unfold row
  rw [←List.ofFn_congr (row_length xs hw),List.ofFn_get]

theorem row_nonblank (xs : Fin R → Coefficient) (hw : ∀ j,(xs j).1.length=w ∧ (xs j).2.length=w)
    (k : Fin (symbols R w)) : row xs hw k≠blank :=
  UnitPhaseFullStreamNormalized.nonblank xs _ (List.get_mem _ _)

def rows (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ActivePrefixStageNativeRows.Rows d (symbols R w) := fun i => row (xs i) (hw i)

theorem rows_nonblank (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i k,rows d xs hw i k≠blank := fun i k => row_nonblank (xs i) (hw i) k

/-- The native stage source is precisely the literal flat coefficient word,
including both separators at every polynomial coefficient. -/
theorem serialized_rows (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    List.ofFn (ActivePrefixStageNativeRows.flat (rows d xs hw))=serialized (flattenArray xs) := by
  change List.ofFn (flattenArray (rows d xs hw))=_
  rw [ofFn_flattenArray]
  have hr : List.ofFn (fun i => List.ofFn (rows d xs hw i))=
      List.ofFn (fun i => serialized (xs i)) := by
    apply congrArg List.ofFn
    funext i
    exact row_word (xs i) (hw i)
  rw [hr]
  unfold serialized
  change _=(List.ofFn (flattenArray (fun i j => encoded (xs i j)))).flatten
  rw [ofFn_flattenArray,List.flatten_flatten,List.map_ofFn]
  rfl

theorem source_head (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativeRows.core d (rows d xs hw)).head 65=0 := rfl

/-- The phase source encoding and native-stage source encoding are literally
the same tape word in the stage alphabet, not a caller-supplied codec premise. -/
theorem source_word (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativeRows.core d (rows d xs hw)).tape 65=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0 (serialized (flattenArray xs))) := by
  change SymbolTriplePlaced.native ActivePrefixStageNative.ha
    (ActivePrefixStageNativeRows.flat (rows d xs hw))=_
  unfold SymbolTriplePlaced.native SymbolTripleClean.word
  rw [serialized_rows]

/-- Address action retains the polynomial index and every stored native digit. -/
theorem action_rows (d : Inputs s) (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ActivePrefixStageNativeRows.action d (rows d xs hw)=
      rows d (fun i j => xs (ActivePrefixStageNativeRows.rowDestination d i) j)
        (fun i j => hw (ActivePrefixStageNativeRows.rowDestination d i) j) := rfl

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial
