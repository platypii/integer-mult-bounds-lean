import IntegerMultBounds.Machine.NativePolynomialConjugation
import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.CompactNativeRoleTransferBudget
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid

/-! Physical native-row conjugation on any literal caller slot. The scanner
changes only that tape, returns its head to zero and pays a uniform full-row
volume bound. Actual inherited-grid guards certify signed complex semantics. -/
namespace IntegerMultBounds.Machine.NativePolynomialConjugationRows
noncomputable section
open ButterflyStreamData (Coefficient)
open NativePolynomialConjugationData (negative coefficient array negative_length)
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)

theorem records_ofFn {N : ℕ} (f : Fin N → Coefficient) :
    NativePolynomialConjugation.records (List.ofFn f)=NativeZeroPaddingArray.word f := by
  simp only [NativePolynomialConjugation.records,NativeZeroPaddingArray.word,List.map_ofFn,Function.comp_def]

theorem bank_ofFn {N : ℕ} (f : Fin N → Coefficient) :
    NativePolynomialConjugation.bank (List.ofFn f)=
      FiniteReturnStack.bank (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) 0 := by
  rw [NativePolynomialConjugation.bank,records_ofFn]
  rfl

def program {t : ℕ} (slot : Fin t) :=
  Placement.placed NativePolynomialConjugation.program (FiniteReturnStackAt.placement slot)

theorem runs {t N : ℕ} (slot : Fin t) (v : Tapes t 2) (f : Fin N → Coefficient)
    (hs : v.tape slot=NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hh : v.head slot=0) :
    HoareTime (program slot) (fun w => w=v)
      (fun w => w=setTape v slot (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0)
      (2*(NativeZeroPaddingArray.word f).length+3) := by
  have h := Placement.hoare_at (NativePolynomialConjugation.runs (List.ofFn f))
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,hs,hh,bank_ofFn])
  rw [records_ofFn] at h
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [List.map_ofFn]
  change Placement.replace (FiniteReturnStackAt.placement slot) v
    (NativePolynomialConjugation.bank (List.ofFn (array f))) = _
  rw [bank_ofFn,FiniteReturnStackAt.replace_bank]

theorem frame {t N : ℕ} (slot i : Fin t) (hi : i≠slot) (v : Tapes t 2)
    (f : Fin N → Coefficient) :
    (setTape v slot (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0).head i=v.head i ∧
    (setTape v slot (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0).tape i=v.tape i := by
  simp [setTape,hi]

private theorem records_length (xs : List Coefficient) (w : ℕ)
    (hw : ∀ x∈xs,x.1.length=w ∧ x.2.length=w) :
    (NativePolynomialConjugation.records xs).length=xs.length*(2*(w+1)) := by
  induction xs with
  | nil => simp [NativePolynomialConjugation.records]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    simp only [NativePolynomialConjugation.records,List.map_cons,List.flatten_cons,List.length_append,
      ButterflyStreamData.encoded,DelimitedRadixRecord.complex_length _ _ _ hx.1 hx.2,
      List.length_cons] at ht ⊢
    rw [ht]
    ring

theorem word_volume (sh : Shape) (rows ell p : ℕ) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    (NativeZeroPaddingArray.word f).length=CompactNativeRoleTransferBudget.volume rows sh ell p := by
  rw [←records_ofFn]
  have h := records_length (List.ofFn f) (CompactNativeRoleHeaders.recordWidth sh p) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hw i)
  simp only [List.length_ofFn] at h
  rw [h]
  rw [CompactSpectatorVisitGeometry.coefficient_count]
  unfold CompactNativeRoleTransferBudget.volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
  ring

theorem runs_linear {t : ℕ} (slot : Fin t) (v : Tapes t 2)
    (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hs : v.tape slot=NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hh : v.head slot=0) :
    HoareTime (program slot) (fun w => w=v)
      (fun w => w=setTape v slot (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0)
      (5*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  have h := runs slot v f hs hh
  rw [word_volume sh rows ell p f hw] at h
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hp := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  change 0<CompactNativeRoleTransferBudget.volume rows sh ell p at hp
  omega

/-- Literal modular conjugation is an involution even before signed guards. -/
theorem negWord_involutive (bs : List Bool) :
    TwosComplement.negWord (TwosComplement.negWord bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simpa only [TwosComplement.negWord] using congrArg (List.cons false) ih
    · simp [TwosComplement.negWord,List.map_map,Function.comp_def]

theorem negative_involutive (xs : List (Fin 2)) : negative (negative xs)=xs := by
  rw [negative,negative,NativePolynomialConjugationData.bits_digits,negWord_involutive,
    NativePolynomialConjugationData.digits_bits]

theorem coefficient_involutive (x : Coefficient) : coefficient (coefficient x)=x := by
  simp only [coefficient,negative_involutive]

theorem array_involutive {N : ℕ} (f : Fin N → Coefficient) : array (array f)=f := by
  funext i
  exact coefficient_involutive (f i)

theorem inherited_width (sh : Shape) (rows ell q : ℕ) (f : Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f) :
    CompactSpectatorInheritedGrid.Width sh rows ell q (array f) := by
  intro i
  simpa only [array,coefficient,negative_length] using hw i

/-- The actual recursive Path and inherited grid exclude the signed minimum;
no extra scalar guard is requested from the caller. -/
theorem decoded_from_path {sh : Shape} {rows ell q left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    CompactSpectatorInheritedGrid.decoded sh rows ell q n (array f)=
      fun i => star (CompactSpectatorInheritedGrid.decoded sh rows ell q n f i) := by
  funext i
  apply NativePolynomialConjugationData.decoded
  · have h := (hw i).2
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using h
  · exact (CompactSpectatorInheritedGrid.signed_guards_from_path sh rows ell q path p C n hp hchunk f hg i).2

end
end IntegerMultBounds.Machine.NativePolynomialConjugationRows
