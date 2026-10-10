import IntegerMultBounds.Machine.CompactNativeConjugatedPhase

/-! Zero-dimensional edges execute the same physical conjugation table.
The idle phase is paid, and the actual reverse basis restores every digit. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedPhaseZero
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageHeadersData (Order)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge)
open Networks.ComplexPhaseRowSchedule (dimension)
open CompactNativeConjugatedPhase
variable {s : Shape}

def cost (D : ℕ) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (order : Order) (pc : Fin count) (ell w : ℕ)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair d op) D) :=
  wordCost D d (symbols (2^ell) w) hp (ops d hslots pc)+
    AllAxisNativePolynomialCaller.zeroCost order d ell+
    wordCost D d (symbols (2^ell) w) hp (ops d hslots pc).reverse+2

theorem rows_congr (d : Inputs s) (ell w : ℕ)
    (xs ys : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hx : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w)
    (hy : ∀ i j,(ys i j).1.length=w ∧ (ys i j).2.length=w) (h : xs=ys) :
    rows d xs hx=rows d ys hy := by
  subst ys
  rfl

theorem reverse_forward (d : Inputs s) (hslots : d.stage.slots=25^3)
    (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :
    ActivePrefixStageNativePolynomialWord.word d (ops d hslots pc).reverse
      (forward d hslots pc ell xs)=xs := by
  funext r k
  rw [ActivePrefixStageNativePolynomialWord.word_reverse_entry]
  exact ActivePrefixStageNativePolynomialWord.word_destination d (ops d hslots pc) xs r k

/-- A fixed native stage executes zero-dimensional edges with literal input
restoration and a paid forward/idle/reverse lifecycle. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hslots : d.stage.slots=25^3) (order : Order)
      (_ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
      (pc : Fin count) (_hm : dimension (edge pc)=0) (ell w : ℕ)
      (_hcode : s.payload=symbols (2^ell) w*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair d op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
      (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w),
      HoareTime (program P order pc) (fun z => z=bank d ell (rows d xs hw))
        (fun z => z=bank d ell (rows d xs hw))
        (cost D d hslots order pc ell w hp) ∧
      (cost D d hslots order pc ell w hp : ℝ)≤
        2*((Networks.ComplexPhaseRowSchedule.word (edge pc)).length : ℝ)*C*
          ActivePrefixStageInverseBudget.scale d+
          (AllAxisNativePolynomialCaller.zeroCost order d ell : ℝ)+2 := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexPhaseFixedWord.exists_fixed_program D
  refine ⟨q,P,C,hC,?_⟩
  intro s d hslots order ho pc hm ell w hcode hp xs hw
  obtain ⟨hf,hfRun,_,_⟩ := hP s (symbols (2^ell) w) d hslots hcode hp (edge pc)
    (rows d xs hw) (ActivePrefixStageNativePolynomial.rows_nonblank d xs hw)
  rw [ActivePrefixStageNativePolynomialWord.result_rows] at hfRun
  have hforward := hoare_extend_eq (hoare_extend_eq hfRun (AllAxisPhaseOriginalScalar.scalar ell))
    (FixedHeaderBankCopy.empty 67)
  have hphase := AllAxisNativePolynomialCaller.zero_runs order d ho pc hm ell w
    (forward d hslots pc ell xs) (forward_width d hslots pc ell w xs hw)
  obtain ⟨_,_,hb,hbRun⟩ := hP s (symbols (2^ell) w) d hslots hcode hp (edge pc)
    (rows d (forward d hslots pc ell xs) (forward_width d hslots pc ell w xs hw))
    (ActivePrefixStageNativePolynomial.rows_nonblank d _ _)
  rw [ActivePrefixStageNativePolynomialWord.result_rows] at hbRun
  have he := reverse_forward d hslots pc ell xs
  dsimp only [ops] at he
  have hr := rows_congr d ell w _ xs
    (ActivePrefixStageNativePolynomialWord.word_width d
      (CompactComplexPhasePhysical.word d hslots (edge pc)).reverse _
      (forward_width d hslots pc ell w xs hw)) hw he
  rw [hr] at hbRun
  have hreverse := hoare_extend_eq (hoare_extend_eq hbRun (AllAxisPhaseOriginalScalar.scalar ell))
    (FixedHeaderBankCopy.empty 67)
  change HoareTime (framedForward P pc) (fun z => z=bank d ell (rows d xs hw))
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs)
      (forward_width d hslots pc ell w xs hw)))
    (wordCost D d (symbols (2^ell) w) hp (ops d hslots pc)) at hforward
  change HoareTime (AllAxisNativePolynomialCaller.program order pc)
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs)
      (forward_width d hslots pc ell w xs hw)))
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs)
      (forward_width d hslots pc ell w xs hw)))
    (AllAxisNativePolynomialCaller.zeroCost order d ell) at hphase
  change HoareTime (framedReverse P pc)
    (fun z => z=bank d ell (rows d (forward d hslots pc ell xs)
      (forward_width d hslots pc ell w xs hw)))
    (fun z => z=bank d ell (rows d xs hw))
    (wordCost D d (symbols (2^ell) w) hp (ops d hslots pc).reverse) at hreverse
  constructor
  · exact (hforward.seq (hphase.seq hreverse)).consequence
      (fun _ hz => hz) (fun _ hz => hz) (by unfold cost; omega)
  · dsimp only [cost,wordCost]
    push_cast
    dsimp only [ops] at *
    linarith

end
end IntegerMultBounds.Machine.CompactNativeConjugatedPhaseZero
