import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersRun

/-! Arbitrary canonical original geometry words are retained literally;
constructed highest-bit consumer words are canonical binary numerals. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersEndpoint
noncomputable section
open ActiveTargetHighestPairData ActiveTargetHighestPairHeadersData
open ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def input (hs : Fin 5 → List Bool) : Tapes 43 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 38 a)
def words (g : Geometry) : Fin 10 → List Bool := fun i => bits (values g i)

theorem canonical_originals (g : Geometry) (hs : Fin 5 → List Bool)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) : hs=fun i => bits (originalValues g i) := by
  funext i
  exact CompactGadgetReservationHeadersCore.canonical_bits _ _ (hc i) (hv i)

theorem input_eq (g : Geometry) (hs : Fin 5 → List Bool)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) : input (a := a) hs=bank (initial g) := by
  rw [canonical_originals g hs hv hc]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem words_value (g : Geometry) : ∀ i,Counter.value (words g i)=values g i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (g : Geometry) : ∀ i,GrowingCounterData.Canonical (words g i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _

theorem produces (g : Geometry) (hs : Fin 5 → List Bool)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (ActiveTargetHighestPairHeadersRun.program (a := a)) (fun v => v=input hs)
      (fun v => v=bank (finished g)) (ActiveTargetHighestPairHeadersRun.cost g) := by
  rw [input_eq g hs hv hc]
  exact ActiveTargetHighestPairHeadersRun.runs g

theorem cleans (g : Geometry) (hs : Fin 5 → List Bool)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (ActiveTargetHighestPairHeadersRun.cleanupProgram (a := a)) (fun v => v=bank (finished g))
      (fun v => v=input hs) (ActiveTargetHighestPairHeadersRun.cleanupCost g) := by
  rw [input_eq g hs hv hc]
  exact ActiveTargetHighestPairHeadersRun.cleans g

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersEndpoint
