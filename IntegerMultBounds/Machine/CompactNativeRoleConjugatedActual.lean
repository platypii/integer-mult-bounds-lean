import IntegerMultBounds.Machine.CompactNativePolynomialStagePacked
import IntegerMultBounds.Machine.CompactNativeRoleConjugatedLifecycle

/-! One actual phase lifecycle handles all multiplier descendants eventually,
with packed repair proved from original geometry and literal polynomial codec
capacity. Its only scalar allowance concerns the actual retained signed width;
physical controller propagation and recursive network composition remain open. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleConjugatedActual
noncomputable section
open Sizes
open CompactActualStageAllowance CompactGlobalRowPadding CompactReservationCutoff
open ActivePrefixStageParameters (Stage)
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleConjugatedLifecycle
open CompactNativeRoleConjugatedCaller (order)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count)

/-- Literal selected-role endpoints and a paid stage-scale bound for every
actual finite phase edge. Original metadata is restored by the executed
machine itself, rather than a caller-provided preparation or phase routine. -/
def Spec {q t c : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (C : ℝ)
    (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
    {s : Shape} (v : Stage s) (rowsCount ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rowsCount)
    (hslots : v.slots=25^3) : Prop :=
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  let hs := (input_slots v rowsCount ell p hG hGK hr).trans hslots
  ∀ (pc : Fin count)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width s p ∧
      (xs i k).2.length=NativePolynomialStageShape.width s p)
    (_hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
      (List.ofFn (ActivePrefixStageNativeRows.flat (rows d xs hw))))
    (_hhead : payload.head ⟨j.val+1,by omega⟩=0),
    ∃ time : ℕ,
      HoareTime (program P t c j (order v) pc)
        (fun z => z=(caller old ht v rowsCount ell p payload).append (FixedHeaderBankCopy.empty privateTapes))
        (fun z => z=(caller old ht v rowsCount ell p
          (resultPayload d hs pc ell (NativePolynomialStageShape.width s p) xs hw payload j)).append
            (FixedHeaderBankCopy.empty privateTapes)) time ∧
      (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d

/-- A single fixed basis witness works for every actual descendant, original
role bank, selected role and phase edge. Original cutoff and row-depth bounds
supply readiness and all rewritten-pair repair prerequisites at density one. -/
theorem eventually_exists_program (arity m : ℕ) (hc : 2≤arity) (hm : 2≤m) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D level p : ℕ) (_hcut : cutoff arity m n≤D) (_hD : D≤d n)
      (_hj : level≤depth m (d n))
      (v : Stage (actualShape n arity m D 1))
      (_hw : b n≤NativePolynomialStageShape.width (actualShape n arity m D 1) p)
      (hslots : v.slots=25^3)
      (t c : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c),
      ∃ (hG : 1≤(actualShape n arity m D 1).guard)
        (hGK : (actualShape n arity m D 1).guard+1≤(actualShape n arity m D 1).chunk)
        (hr : 0<rowsAt arity m (d n) (K n) level),
        Spec P C old ht payload j v (rowsAt arity m (d n) (K n) level) (ℓ n) p hG hGK hr hslots := by
  obtain ⟨q,P,C,hC,hP⟩ := exists_program 1
  refine ⟨q,P,C,hC,?_⟩
  filter_upwards [CompactNativePolynomialStagePacked.eventually_ready_packed arity m hc hm] with n hp
  intro D level p hcut hD hj v hw hslots t c old ht payload j
  obtain ⟨hG,hGK,hr,hpacked⟩ := hp D level p hcut hD hj v hw
  refine ⟨hG,hGK,hr,?_⟩
  dsimp only [Spec]
  intro pc xs hwidth hword hhead
  obtain ⟨hrun,hbound⟩ := hP t c old ht payload j _ v _ (ℓ n) p hG hGK hr rfl hslots pc
    (fun op _ => hpacked op) xs hwidth hword hhead
  exact ⟨_,hrun,hbound⟩

end
end IntegerMultBounds.Machine.CompactNativeRoleConjugatedActual
