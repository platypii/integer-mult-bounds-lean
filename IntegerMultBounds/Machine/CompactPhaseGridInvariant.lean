import IntegerMultBounds.Machine.AllAxisPolynomialTensorResult
import IntegerMultBounds.Machine.CompactComplexScalarGrid

/-! Actual aggregate signed phase execution preserves its incoming precision
and numerator budget. Role selection, copying and zero padding also preserve
that invariant; arithmetic growth is accounted separately by scalar prefixes. -/
namespace IntegerMultBounds.Machine.CompactPhaseGridInvariant
noncomputable section
open Networks Networks.GaussianPrecision
open ButterflySigned
open ButterflyStreamData (Coefficient)

/-- Strict signed arithmetic guard from the current actual numerator budget. -/
theorem strict_guard (a : Coefficient) (b n M : ℕ)
    (hgrid : BoundedGrid n M (complexValue (signedValue b a.1) (signedValue b a.2) n))
    (hM : M<2^b) :
    ∀ i : Fin 2,|signedValue b (UnitPhasePolynomialArray.components a i.val)|<(2^b : ℕ) := by
  have h := ButterflyGuard.represented_bound _ _ n M hgrid
  have hM' : (M:ℤ)<(2^b:ℕ) := by exact_mod_cast hM
  intro i
  fin_cases i
  · exact h.1.trans_lt hM'
  · exact h.2.trans_lt hM'

/-- The literal signed words emitted by the actual coefficient kernel retain
exactly the same grid and numerator bound, with no precision increment. -/
theorem signed_phase (q : Fin 4) (a : Coefficient) (b n M : ℕ)
    (hw : a.1.length=b+1 ∧ a.2.length=b+1)
    (hgrid : BoundedGrid n M (complexValue (signedValue b a.1) (signedValue b a.2) n))
    (hM : M<2^b) :
    BoundedGrid n M (complexValue
      (signedValue b (UnitPhaseNumerator.words q 0 (UnitPhasePolynomialArray.components a)))
      (signedValue b (UnitPhaseNumerator.words q 1 (UnitPhasePolynomialArray.components a))) n) := by
  have hc : ∀ j,(UnitPhasePolynomialArray.components a j).length=b+1 := by
    intro j
    unfold UnitPhasePolynomialArray.components
    split_ifs <;> first | exact hw.1 | exact hw.2
  rw [UnitPhaseSigned.words_phase q _ b n hc (strict_guard a b n M hgrid hM)]
  exact bounded_phase_mul _ hgrid

/-- The whole-array stream's real quotient-indexed output inherits the exact
incoming grid at each coefficient, including every polynomial spectator. -/
theorem stream_result {s : CompactGadgetReservationShape.Shape}
    (v : ActivePrefixStageParameters.Stage s) (m : ℕ) (ws : List (ZMod 4))
    {N R : ℕ} (xs : Fin (N*R) → Coefficient) (b n M : ℕ)
    (hw : ∀ i,(xs i).1.length=b+1 ∧ (xs i).2.length=b+1)
    (hg : ∀ i,BoundedGrid n M (complexValue (signedValue b (xs i).1) (signedValue b (xs i).2) n))
    (hM : M<2^b) (i : Fin (N*R)) :
    BoundedGrid n M (complexValue
      (signedValue b (AllAxisPolynomialLiteralEndpoint.result v m ws xs i).1)
      (signedValue b (AllAxisPolynomialLiteralEndpoint.result v m ws xs i).2) n) :=
  signed_phase _ (xs i) b n M (hw i) (hg i) hM

theorem reindex {ι κ : Type*} (f : ι → Coefficient) (pick : κ → ι) (b n M : ℕ)
    (hf : ∀ i,BoundedGrid n M (complexValue (signedValue b (f i).1) (signedValue b (f i).2) n)) :
    ∀ j,BoundedGrid n M (complexValue (signedValue b (f (pick j)).1) (signedValue b (f (pick j)).2) n) :=
  fun j => hf (pick j)

/-- Genuine zeros inserted by role padding satisfy every current grid budget. -/
theorem padded {ι κ : Type*} (f : ι → ℂ) (pick : κ → Option ι) (n M : ℕ)
    (hf : ∀ i,BoundedGrid n M (f i)) :
    ∀ j,BoundedGrid n M ((pick j).elim 0 f) := by
  intro j
  cases pick j with
  | none => exact bounded_zero n M
  | some i => exact hf i

end
end IntegerMultBounds.Machine.CompactPhaseGridInvariant
