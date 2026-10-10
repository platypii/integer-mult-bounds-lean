import IntegerMultBounds.Machine.CompactComplexRolePhaseContinuation
import IntegerMultBounds.Machine.CompactNativeRoleConjugatedActual

/-! Actual multiplier geometry supplies readiness and packed repair for every
real complex25 occurrence's original named role. Retained stored width and
literal coefficient word/head remain explicit controller invariants. -/
namespace IntegerMultBounds.Machine.CompactComplexRolePhaseActual
noncomputable section
open Sizes
open CompactActualStageAllowance CompactGlobalRowPadding CompactReservationCutoff
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageFullData (Inputs)
open CompactComplexRecursiveGeometry (Visit node arity)
open Networks.ComplexRecursiveCallSchema (Occurrence)
open CompactComplexRolePhaseSite (roleCount role pc)
open CompactNativeRoleConjugatedLifecycle (caller resultPayload privateTapes input_slots)
open CompactNativeRoleConjugatedCaller (order)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {t : ℕ}

def Spec {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (C : ℝ)
    (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+roleCount) 2) (site : Occurrence)
    (v : Stage s) (rowsCount ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rowsCount) (hslots : v.slots=25^3) : Prop :=
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  let hs := (input_slots v rowsCount ell p hG hGK hr).trans hslots
  ∀ (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width s p ∧
      (xs i k).2.length=NativePolynomialStageShape.width s p)
    (_hword : payload.tape ⟨(role site).val+1,by have := (role site).isLt; omega⟩=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat (rows d xs hw))))
    (_hhead : payload.head ⟨(role site).val+1,by have := (role site).isLt; omega⟩=0),
    ∃ time : ℕ,
      HoareTime (CompactComplexRolePhaseSite.program P t site (order v))
        (fun z => z=(caller old ht v rowsCount ell p payload).append (FixedHeaderBankCopy.empty privateTapes))
        (fun z => z=(caller old ht v rowsCount ell p
          (resultPayload d hs (pc site) ell (NativePolynomialStageShape.width s p) xs hw payload (role site))).append
            (FixedHeaderBankCopy.empty privateTapes)) time ∧
      (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d ∧
      ∀ (k : ℕ) (K : Program (CompactComplexRolePhaseContinuation.tapes t) k prime) (entry : Fin 2),
        CompactComplexRolePhaseContinuation.Block.Reached
          (CompactComplexRolePhaseSite.program P t site (order v)) K entry
          ((caller old ht v rowsCount ell p payload).append (FixedHeaderBankCopy.empty privateTapes))
          ((caller old ht v rowsCount ell p
            (resultPayload d hs (pc site) ell (NativePolynomialStageShape.width s p) xs hw payload (role site))).append
              (FixedHeaderBankCopy.empty privateTapes)) time

/-- The proved actual native lifecycle supplies the phase of each original
network occurrence. Node slots, readiness and every pair repair are derived. -/
theorem eventually_exists_program (base m : ℕ) (hc : 2≤base) (hm : 2≤m) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D level p : ℕ) (_hcut : cutoff base m n≤D) (_hD : D≤d n) (_hj : level≤depth m (d n))
      (rho : Fin (actualShape n base m D 1).chunk) (left k : ℕ)
      (visit : Visit (actualShape n base m D 1).active left (k+1))
      (hactive : (actualShape n base m D 1).active≤(actualShape n base m D 1).axes)
      (pair : Networks.BinaryRowProgram.Op (Fin arity))
      (_hw : b n≤NativePolynomialStageShape.width (actualShape n base m D 1) p)
      (t : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+roleCount) 2) (site : Occurrence),
      ∃ (hG : 1≤(actualShape n base m D 1).guard)
        (hGK : (actualShape n base m D 1).guard+1≤(actualShape n base m D 1).chunk)
        (hr : 0<rowsAt base m (d n) (K n) level),
        Spec P C old ht payload site (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair)
          (rowsAt base m (d n) (K n) level) (ℓ n) p hG hGK hr rfl := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactNativeRoleConjugatedActual.eventually_exists_program base m hc hm
  refine ⟨q,P,C,hC,?_⟩
  filter_upwards [hP] with n hp
  intro D level p hcut hD hj rho left k visit hactive pair hw t old ht payload site
  obtain ⟨hG,hGK,hr,hsite⟩ := hp D level p hcut hD hj
    (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) hw rfl t roleCount old ht payload (role site)
  refine ⟨hG,hGK,hr,?_⟩
  dsimp only [Spec]
  intro xs hwidth hword hhead
  obtain ⟨time,hrun,hbound⟩ := hsite (pc site) xs hwidth hword hhead
  refine ⟨time,hrun,hbound,?_⟩
  intro k K entry
  exact CompactComplexRolePhaseContinuation.ready P site _ K entry _ _ time hrun

end
end IntegerMultBounds.Machine.CompactComplexRolePhaseActual
