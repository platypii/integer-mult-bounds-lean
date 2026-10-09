import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget

/-! Arbitrary canonical original words are retained exactly. Ten constructed
outputs are canonical, and the complete arithmetic workspace is restored. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersEndpoint
noncomputable section
open ActivePrefixLayoutHeadersData ActivePrefixLayoutHeadersRun ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def input (hs : Fin 14 → List Bool) : Tapes 43 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 29 a)
def words (mode : Mode) (d : Inputs) : Fin 10 → List Bool := fun i => bits (values mode d i)

theorem canonical_originals (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) : hs=fun i => bits (originalValues d i) := by
  funext i
  exact CompactGadgetReservationHeadersCore.canonical_bits _ _ (hc i) (hv i)

theorem input_eq (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) : input (a := a) hs=bank (initial d) := by
  rw [canonical_originals d hs hv hc]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem words_value (mode : Mode) (d : Inputs) : ∀ i, Counter.value (words mode d i)=values mode d i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (mode : Mode) (d : Inputs) : ∀ i, GrowingCounterData.Canonical (words mode d i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _

theorem produces (mode : Mode) (d : Inputs) (hw : d.w≤d.H) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (A : ℕ) (hA : 0<A) (hp : 0<d.payload) (ho : ∀ i, originalValues d i≤A) (hS : suffix mode d≤A) :
    HoareTime (program (a := a) mode) (fun v => v=input hs)
      (fun v => v=bank (finished mode d)) (ActivePrefixLayoutHeadersBudget.constant*A) := by
  rw [input_eq d hs hv hc]
  exact (runs mode d hw).consequence (fun _ h => h) (fun _ h => h)
    (ActivePrefixLayoutHeadersBudget.cost_bound mode d A hA hp ho hS)

theorem cleans (mode : Mode) (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (A : ℕ) (hA : 0<A) (ho : ∀ i, originalValues d i≤A) (hS : suffix mode d≤A) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished mode d))
      (fun v => v=input hs) (ActivePrefixLayoutHeadersBudget.cleanupConstant*A) := by
  rw [input_eq d hs hv hc]
  exact (ActivePrefixLayoutHeadersRun.cleans mode d).consequence (fun _ h => h) (fun _ h => h)
    (ActivePrefixLayoutHeadersBudget.cleanup_bound mode d A hA ho hS)

theorem outputs (mode : Mode) (d : Inputs) (j : Fin 10) :
    (bank (a := a) (finished mode d)).tape (Fin.castAdd 15 (Fin.natAdd 14 (Fin.castAdd 4 j)))=
      RadixZeroFill.encodedBinary (words mode d j) ∧
    (bank (a := a) (finished mode d)).head (Fin.castAdd 15 (Fin.natAdd 14 (Fin.castAdd 4 j)))=1 := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem originals_retained (mode : Mode) (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 14) :
    (bank (a := a) (finished mode d)).head (Fin.castAdd 29 j)=(input (a := a) hs).head (Fin.castAdd 29 j) ∧
    (bank (a := a) (finished mode d)).tape (Fin.castAdd 29 j)=(input (a := a) hs).tape (Fin.castAdd 29 j) := by
  rw [input_eq d hs hv hc]
  fin_cases j <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersEndpoint
