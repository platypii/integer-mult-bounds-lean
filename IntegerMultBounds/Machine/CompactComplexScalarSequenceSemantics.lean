import IntegerMultBounds.Machine.CompactComplexScalarPolynomialSequence

/-! Literal complete scalar-array sequences have the original named complex
circuit semantics. One initial numerator reserve pays every subsequent row;
no intermediate signed guards or numerical stream callback are supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarSequenceSemantics
noncomputable section
open CompactComplexScalarIntegerRows (RowIndex Wire wireIndex gate guardBits)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarPolynomialRows (result)
open CompactComplexScalarPolynomialSequence (execute)
open ButterflyStreamData (Coefficient)
open ButterflySigned (signedValue complexValue)
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

def Bound {N : ℕ} (b p : ℕ) (data : Fin wireCount → Fin N → Coefficient) : Prop :=
  ∀ j i,|signedValue b (data j i).1|≤((2^p:ℕ):ℤ) ∧
    |signedValue b (data j i).2|≤((2^p:ℕ):ℤ)

def values {N : ℕ} (b n : ℕ) (data : Fin wireCount → Fin N → Coefficient)
    (i : Fin N) : Wire → ℂ := fun wire =>
  complexValue (signedValue b (data (wireIndex wire) i).1)
    (signedValue b (data (wireIndex wire) i).2) n

def circuit (ops : List RowIndex) := ops.map (fun r => Networks.RationalScalarGrid.castGate (gate r))

theorem row_values {N : ℕ} (r : RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (b p n : ℕ) (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+guardBits≤b) (i : Fin N) :
    values b (n+1) (result r data) i=
      (Networks.RationalScalarGrid.castGate (gate r)).run (values b n data i) := by
  funext wire
  unfold values
  simpa only [values,Equiv.symm_apply_apply] using
    CompactComplexScalarPolynomialRows.result_semantics r data b p n hw
      (fun j i => (hb j i).1) (fun j i => (hb j i).2) hg (wireIndex wire) i

theorem row_bound {N : ℕ} (r : RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (b p : ℕ) (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+guardBits≤b) : Bound b (p+guardBits) (result r data) := by
  intro j i
  have h := CompactComplexScalarPolynomialRows.result_semantics r data b p 0 hw
    (fun j i => (hb j i).1) (fun j i => (hb j i).2) hg j i
  rw [CompactComplexScalarIntegerRows.row_semantics] at h
  have he := ButterflyGuard.numerators_unique _ _ _ _ 1 h
  rw [he.1,he.2]
  exact ⟨(CompactComplexScalarIntegerRows.uniform_numerator_guard r _ p
      (fun wire => (hb (wireIndex wire) i).1) _).le,
    (CompactComplexScalarIntegerRows.uniform_numerator_guard r _ p
      (fun wire => (hb (wireIndex wire) i).2) _).le⟩

private theorem reserve_step (p len g b : ℕ) (hg : p+(len+1)*g≤b) :
    p+g≤b ∧ (p+g)+len*g≤b := by
  rw [Nat.add_mul, Nat.one_mul] at hg
  omega

/-- The complete block retains its field widths and supplies the final
numerator bound required by the next recursive event. -/
theorem sequence_bound {N : ℕ} (ops : List RowIndex)
    (data : Fin wireCount → Fin N → Coefficient) (b p : ℕ)
    (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+ops.length*guardBits≤b) :
    (∀ j i,(execute ops data j i).1.length=b+1 ∧
      (execute ops data j i).2.length=b+1) ∧
    Bound b (p+ops.length*guardBits) (execute ops data) := by
  induction ops generalizing data p with
  | nil =>
    change (∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1) ∧ Bound b (p+0*guardBits) data
    simpa only [zero_mul, add_zero] using And.intro hw hb
  | cons r ops ih =>
    have hreserve := reserve_step p ops.length guardBits b (by simpa only [List.length_cons] using hg)
    have hwidth := CompactComplexScalarPolynomialRows.result_width r data (b+1) hw
    have hbound := row_bound r data b p hw hb hreserve.1
    have htail := ih (result r data) (p+guardBits) hwidth hbound hreserve.2
    have hp : p+(r::ops).length*guardBits=(p+guardBits)+ops.length*guardBits := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    rw [hp]
    exact htail

/-- Every intermediate signed guard follows from the initial finite-row
reserve, and every completed row advances one common denominator. -/
theorem sequence_values {N : ℕ} (ops : List RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (b p n : ℕ) (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+ops.length*guardBits≤b) (i : Fin N) :
    values b (n+ops.length) (execute ops data) i=
      Networks.Circuit.run (circuit ops) (values b n data i) := by
  induction ops generalizing data p n with
  | nil => rfl
  | cons r ops ih =>
    have hreserve := reserve_step p ops.length guardBits b (by simpa only [List.length_cons] using hg)
    have hwidth := CompactComplexScalarPolynomialRows.result_width r data (b+1) hw
    have hbound := row_bound r data b p hw hb hreserve.1
    have htail := ih (result r data) (p+guardBits) (n+1) hwidth hbound hreserve.2
    have hexec : execute (r::ops) data=execute ops (result r data) := rfl
    rw [hexec]
    have hn : n+(r::ops).length=(n+1)+ops.length := by simp only [List.length_cons]; omega
    rw [hn,htail,row_values r data b p n hw hb hreserve.1 i]
    rfl

end
end IntegerMultBounds.Machine.CompactComplexScalarSequenceSemantics
