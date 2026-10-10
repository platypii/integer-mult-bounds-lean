import IntegerMultBounds.Machine.CompactNativeConjugatedPhaseFamily
import IntegerMultBounds.Machine.FiniteKernelDispatchAlphabet

/-! One physical finite table dispatches every actual complex25 conjugated
phase, including zero-dimensional edges, on the original native polynomial
bank. Call sites write their literal edge token; execution erases it and all
phase workspace. The complete shared table has one uniform stage-scale bound. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedPhaseDispatch
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageHeadersData (Order)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge capacity)
open CompactNativeConjugatedPhase (bank)
open CompactNativeConjugatedPhaseFamily (output cost)

abbrev tapes := AllAxisPhaseOriginalScalar.outer+67

def kernels {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (order : Order)
    (pc : Fin count) : FiniteKernelDispatchAlphabet.Kernel tapes prime :=
  ⟨_,CompactNativeConjugatedPhase.program P order pc⟩
def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (order : Order) :=
  FiniteKernelDispatchAlphabet.program capacity (kernels P order)
def call {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (order : Order) (pc : Fin count) :=
  FiniteKernelDispatchAlphabet.call capacity (kernels P order) pc

def token (pc : Fin count) : Tapes 1 prime := FiniteKernelDispatchAlphabet.token capacity pc

private theorem overhead_bound (B k : ℕ) (C S : ℝ) (hB : (B : ℝ)≤C*S) (hS : 1≤S) :
    ((k+B : ℕ) : ℝ)≤(C+(k : ℝ))*S := by
  have hK := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg k : (0 : ℝ)≤k)
  calc
    ((k+B : ℕ) : ℝ)=(k : ℝ)+(B : ℝ) := Nat.cast_add k B
    _≤(k : ℝ)*S+C*S := add_le_add (by simpa only [mul_one] using hK) hB
    _=(C+(k : ℝ))*S := by ring

/-- Every actual edge uses the same finite native dispatcher and stage witness.
The token is physically installed by each call site, rather than assumed as
an oracle input. Both token lifecycles have a uniform paid runtime. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hslots : d.stage.slots=25^3) (order : Order)
      (_ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
      (pc : Fin count) (ell w : ℕ)
      (_hcode : s.payload=symbols (2^ell) w*3+0)
      (_hR : 2^ell≤s.payload) (_hwV : 2^ell*w≤s.payload)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair d op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
      (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w),
      HoareTime (program P order)
        (fun z => z=(bank d ell (rows d xs hw)).append (token pc))
        (fun z => z=(output d hslots pc ell w xs hw).append (SharedBank.empty 1 prime))
        (count+2+cost D d hslots order pc ell w hp) ∧
      HoareTime (call P order pc)
        (fun z => z=(bank d ell (rows d xs hw)).append (SharedBank.empty 1 prime))
        (fun z => z=(output d hslots pc ell w xs hw).append (SharedBank.empty 1 prime))
        (2*count+3+cost D d hslots order pc ell w hp) ∧
      ((2*count+3+cost D d hslots order pc ell w hp : ℕ) : ℝ)≤
        C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactNativeConjugatedPhaseFamily.exists_program D
  refine ⟨q,P,C+((2*count+3 : ℕ) : ℝ),
    add_pos_of_pos_of_nonneg hC (Nat.cast_nonneg _),?_⟩
  intro s d hslots order ho pc ell w hcode hR hwV hp xs hw
  obtain ⟨hrun,hbound⟩ := hP s d hslots order ho pc ell w hcode hR hwV hp xs hw
  refine ⟨FiniteKernelDispatchAlphabet.runs capacity (kernels P order) pc _ _ _ hrun,
    FiniteKernelDispatchAlphabet.call_runs capacity (kernels P order) pc _ _ _ hrun,?_⟩
  exact overhead_bound _ (2*count+3) C _ hbound (ActivePrefixStageInverseBudget.one_le_scale d)

end
end IntegerMultBounds.Machine.CompactNativeConjugatedPhaseDispatch
