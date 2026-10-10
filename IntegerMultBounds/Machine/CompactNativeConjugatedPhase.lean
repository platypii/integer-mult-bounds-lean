import IntegerMultBounds.Machine.CompactComplexPhaseFixedWord
import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomialWord
import IntegerMultBounds.Machine.AllAxisNativePolynomialCaller

/-! Physical forward basis, aggregate tensor phase and reversed basis on the
original native polynomial source. Both basis machines are fixed per finite
edge; every original header, immutable ell and private phase tape is restored.
The runtime includes all three machines and both sequencing transitions. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageHeadersData (Order)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge)
open Networks.ComplexPhaseRowSchedule (dimension)
variable {s : Shape}


def ops (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) :=
  CompactComplexPhasePhysical.word d hslots (edge pc)
def forward (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :=
  ActivePrefixStageNativePolynomialWord.word d (ops d hslots pc) xs

def phase (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :=
  AllAxisNativePolynomialData.result d ell (dimension (edge pc))
    (CompactComplexPhaseControlCodec.weights (edge pc)).reverse (forward d hslots pc ell xs)
def result (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :=
  ActivePrefixStageNativePolynomialWord.word d (ops d hslots pc).reverse (phase d hslots pc ell xs)

theorem forward_width (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(forward d hslots pc ell xs i j).1.length=w ∧ (forward d hslots pc ell xs i j).2.length=w :=
  ActivePrefixStageNativePolynomialWord.word_width d (ops d hslots pc) xs hw

theorem phase_width (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(phase d hslots pc ell xs i j).1.length=w ∧ (phase d hslots pc ell xs i j).2.length=w :=
  AllAxisNativePolynomialData.result_width d ell (dimension (edge pc)) w
    (CompactComplexPhaseControlCodec.weights (edge pc)).reverse _ (forward_width d hslots pc ell w xs hw)
theorem result_width (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(result d hslots pc ell xs i j).1.length=w ∧ (result d hslots pc ell xs i j).2.length=w :=
  ActivePrefixStageNativePolynomialWord.word_width d (ops d hslots pc).reverse _ (phase_width d hslots pc ell w xs hw)

def framedForward {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (pc : Fin count) :=
  extend (extend (CompactComplexPhaseFixedWord.fixed P (edge pc)).2 1) 67
def framedReverse {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (pc : Fin count) :=
  extend (extend (CompactComplexPhaseFixedWord.compiled P
    (Networks.ComplexPhaseRowSchedule.word (edge pc)).reverse).2 1) 67

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (order : Order) (pc : Fin count) :=
  seq (framedForward P pc) (seq (AllAxisNativePolynomialCaller.program order pc) (framedReverse P pc))

def bank (d : Inputs s) (ell : ℕ) {B : ℕ} (xs : ActivePrefixStageNativeRows.Rows d B) :=
  (AllAxisPhaseOriginalScalar.caller d xs ell).append (FixedHeaderBankCopy.empty 67)

def wordCost (D : ℕ) (d : Inputs s) (B : ℕ)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (ws : List (Networks.BinaryRowProgram.Op (Fin d.stage.slots))) :=
  ActivePrefixStageNativePairSchedule.cost (ActivePrefixStageNativePairSchedule.stageCost (B:=B) D d hp) ws

def cost (D : ℕ) (d : Inputs s) (hslots : d.stage.slots=25^3) (order : Order) (pc : Fin count) (ell w : ℕ)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D) :=
  wordCost D d (symbols (2^ell) w) hp (ops d hslots pc)+
    AllAxisNativePolynomialCaller.cost order d pc ell w+
    wordCost D d (symbols (2^ell) w) hp (ops d hslots pc).reverse+2

/-- Actual fixed physical conjugation, without a basis, phase or codec callback. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hslots : d.stage.slots=25^3) (order : Order)
      (_ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
      (pc : Fin count) (_hm : 0<dimension (edge pc)) (ell w : ℕ)
      (_hcode : s.payload=symbols (2^ell) w*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
      (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w),
      HoareTime (program P order pc) (fun z => z=bank d ell (rows d xs hw))
        (fun z => z=bank d ell (rows d (result d hslots pc ell xs) (result_width d hslots pc ell w xs hw)))
        (cost D d hslots order pc ell w hp) ∧
      (cost D d hslots order pc ell w hp : ℝ)≤
        2*((Networks.ComplexPhaseRowSchedule.word (edge pc)).length : ℝ)*C*ActivePrefixStageInverseBudget.scale d+
          (AllAxisNativePolynomialCaller.cost order d pc ell w : ℝ)+2 := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexPhaseFixedWord.exists_fixed_program D
  refine ⟨q,P,C,hC,?_⟩
  intro s d hslots order ho pc hm ell w hcode hp xs hw
  obtain ⟨hf,hfRun,_,_⟩ := hP s (symbols (2^ell) w) d hslots hcode hp (edge pc)
    (rows d xs hw) (ActivePrefixStageNativePolynomial.rows_nonblank d xs hw)
  rw [ActivePrefixStageNativePolynomialWord.result_rows] at hfRun
  have hforward := hoare_extend_eq (hoare_extend_eq hfRun (AllAxisPhaseOriginalScalar.scalar ell))
    (FixedHeaderBankCopy.empty 67)
  have hphase := AllAxisNativePolynomialCaller.runs order d hslots ho pc hm ell w
    (forward d hslots pc ell xs) (forward_width d hslots pc ell w xs hw)
  obtain ⟨_,_,hb,hbRun⟩ := hP s (symbols (2^ell) w) d hslots hcode hp (edge pc)
    (rows d (phase d hslots pc ell xs) (phase_width d hslots pc ell w xs hw))
    (ActivePrefixStageNativePolynomial.rows_nonblank d _ _)
  rw [ActivePrefixStageNativePolynomialWord.result_rows] at hbRun
  have hreverse := hoare_extend_eq (hoare_extend_eq hbRun (AllAxisPhaseOriginalScalar.scalar ell))
    (FixedHeaderBankCopy.empty 67)
  change HoareTime (framedForward P pc) (fun z => z=bank d ell (rows d xs hw))
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs) (forward_width d hslots pc ell w xs hw)))
    (wordCost D d (symbols (2^ell) w) hp (ops d hslots pc)) at hforward
  change HoareTime (AllAxisNativePolynomialCaller.program order pc)
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs) (forward_width d hslots pc ell w xs hw)))
    (fun z => z=bank d ell (rows d (phase d hslots pc ell xs) (phase_width d hslots pc ell w xs hw)))
    (AllAxisNativePolynomialCaller.cost order d pc ell w) at hphase
  change HoareTime (framedReverse P pc)
    (fun z => z=bank d ell (rows d (phase d hslots pc ell xs) (phase_width d hslots pc ell w xs hw)))
    (fun z => z=bank d ell (rows d (result d hslots pc ell xs) (result_width d hslots pc ell w xs hw)))
    (wordCost D d (symbols (2^ell) w) hp (ops d hslots pc).reverse) at hreverse
  have h := hforward.seq (hphase.seq hreverse)
  constructor
  · exact h.consequence (fun _ hz => hz) (fun _ hz => hz) (by unfold cost; omega)
  · dsimp only [cost,wordCost]
    push_cast
    dsimp only [ops] at *
    linarith

/-- Original-row coefficient semantics of the fully reversed output. -/
theorem result_entry (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (j : Fin (2^ell)) :
    result d hslots pc ell xs r j=
      let p := AllAxisPolynomialLiteralEndpoint.phase d.stage (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse
        (ActivePrefixStageNativePairCoordinates.run d (ops d hslots pc) r).val
      (UnitPhaseNumerator.words p 0 (UnitPhasePolynomialArray.components (xs r j)),
        UnitPhaseNumerator.words p 1 (UnitPhasePolynomialArray.components (xs r j))) := by
  exact ActivePrefixStageNativePolynomialWord.conjugated_entry d (ops d hslots pc)
    (fun i zs k =>
      let p := AllAxisPolynomialLiteralEndpoint.phase d.stage (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse i.val
      (UnitPhaseNumerator.words p 0 (UnitPhasePolynomialArray.components (zs k)),
        UnitPhaseNumerator.words p 1 (UnitPhasePolynomialArray.components (zs k)))) xs r j

/-- The physical output is the original signed tensor phase at every retained
polynomial coefficient; the strict guard is obtained from the actual grid. -/
theorem result_phase_of_grid (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count)
    (hm : 0<dimension (edge pc)) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (k : Fin (2^ell))
    (p G j : ℕ) (hj : j≤G)
    (hw : (xs r k).1.length=ButterflyGuard.halfWidth p G+1 ∧ (xs r k).2.length=ButterflyGuard.halfWidth p G+1)
    (hgrid : Networks.GaussianPrecision.BoundedGrid (p+j) ((2^p)*4^j)
      (ButterflySigned.complexValue
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (xs r k).1)
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (xs r k).2) (p+j))) :
    ButterflySigned.complexValue
      (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (result d hslots pc ell xs r k).1)
      (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (result d hslots pc ell xs r k).2) (p+j)=
      (∏ axis : Fin d.stage.f,Networks.BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta d hslots (edge pc) (ActivePrefixStageNativePairCoordinates.start d r) axis))*
      ButterflySigned.complexValue
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (xs r k).1)
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p G) (xs r k).2) (p+j) := by
  rw [result_entry]
  exact AllAxisPolynomialActual.coefficient_phase_of_grid d hslots (edge pc) hm r (xs r k) p G j hj hw hgrid

end
end IntegerMultBounds.Machine.CompactNativeConjugatedPhase
