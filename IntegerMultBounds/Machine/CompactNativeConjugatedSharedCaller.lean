import IntegerMultBounds.Machine.CompactNativeConjugatedHeaderBank

/-! Physically copy original13 and ell, run the actual conjugated native phase
on one shared source, and erase every copied header. Arbitrary persistent
caller tapes remain framed; the displaced private source stays blank. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedSharedCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open ActivePrefixStageHeadersData (Order)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open CompactNativeConjugatedHeaderBank (tapes source initial)
variable {s : Shape} {B t : ℕ}

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (focus : Fin 14 → Fin t) (selected : Fin t) (order : Order)
    (pc : Fin CompactAllAxisPhaseDispatch.count) :=
  seq (CompactNativeConjugatedHeaderBank.setup focus)
    (seq (Placement.placed (CompactNativeConjugatedPhase.program P order pc)
      (SharedPlacementAlphabet.sharedPlacement selected source))
      (CompactNativeConjugatedHeaderBank.cleanup t))

def cost (t : ℕ) (d : Inputs s) (ell phaseCost : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (AllAxisPhaseOriginalScalar.words d ell)+
    phaseCost+FixedHeaderBankCopy.cleanupCost (t:=t) (AllAxisPhaseOriginalScalar.words d ell)+2

/-- The only phase premise is execution of the concrete conjugated program;
setup, sharing and complete metadata cleanup are actual fixed machines. -/
theorem runs {q phaseCost : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (focus : Fin 14 → Fin t) (selected : Fin t) (order : Order)
    (pc : Fin CompactAllAxisPhaseDispatch.count) (v : Tapes t prime)
    (d : Inputs s) (ell : ℕ) (xs ys : Rows d B)
    (hf : ∀ i,v.tape (focus i)=RadixZeroFill.encodedBinary (AllAxisPhaseOriginalScalar.words d ell i))
    (hh : ∀ i,v.head (focus i)=1)
    (hs : v.tape selected=(CompactNativeConjugatedPhase.bank d ell xs).tape source)
    (hp : v.head selected=(CompactNativeConjugatedPhase.bank d ell xs).head source)
    (hphase : HoareTime (CompactNativeConjugatedPhase.program P order pc)
      (fun z => z=CompactNativeConjugatedPhase.bank d ell xs)
      (fun z => z=CompactNativeConjugatedPhase.bank d ell ys) phaseCost) :
    HoareTime (program P focus selected order pc)
      (fun z => z=v.append (FixedHeaderBankCopy.empty tapes))
      (fun z => z=(setTape v selected ((CompactNativeConjugatedPhase.bank d ell ys).tape source)
        ((CompactNativeConjugatedPhase.bank d ell ys).head source)).append (FixedHeaderBankCopy.empty tapes))
      (cost t d ell phaseCost) := by
  have hcopy := CompactNativeConjugatedHeaderBank.setup_runs focus v d ell hf hh
  have hrun := SharedPlacementAlphabet.shared_hoare hphase v selected source (fun _ => blank) 0 hs hp
  rw [CompactNativeConjugatedHeaderBank.bank_without_source,
    CompactNativeConjugatedHeaderBank.bank_without_source] at hrun
  have hclean := CompactNativeConjugatedHeaderBank.cleanup_runs
    (setTape v selected ((CompactNativeConjugatedPhase.bank d ell ys).tape source)
      ((CompactNativeConjugatedPhase.bank d ell ys).head source)) d ell
  exact (hcopy.seq (hrun.seq hclean)).consequence (fun _ hz => hz) (fun _ hz => hz)
    (by unfold cost; omega)

end
end IntegerMultBounds.Machine.CompactNativeConjugatedSharedCaller
