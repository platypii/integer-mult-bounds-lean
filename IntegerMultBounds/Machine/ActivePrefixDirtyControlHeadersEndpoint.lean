import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersRun

/-! Canonical dirty-control headers, with literal original inputs and complete
physical retention. No derived address start is supplied as an input. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersEndpoint
noncomputable section
open ActiveRepairRankHeadersCommands ActivePrefixLayoutHeadersData
open ActivePrefixDirtyControlHeadersData
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

abbrev input := ActivePrefixLayoutHeadersEndpoint.input (a := a)
def words (k : Kind) (d : Inputs) : Fin 10 → List Bool := fun i => bits (values k d i)
abbrev canonical_originals := ActivePrefixLayoutHeadersEndpoint.canonical_originals
abbrev input_eq := ActivePrefixLayoutHeadersEndpoint.input_eq (a := a)
theorem words_value (k : Kind) (d : Inputs) : ∀ i, Counter.value (words k d i)=values k d i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (k : Kind) (d : Inputs) : ∀ i, GrowingCounterData.Canonical (words k d i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _
abbrev produces := ActivePrefixDirtyControlHeadersRun.produces (a := a)

theorem cleans (k : Kind) (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (ActivePrefixDirtyControlHeadersRun.cleanupProgram (a := a))
      (fun v => v=bank (finished k d)) (fun v => v=input hs)
      (ActivePrefixDirtyControlHeadersRun.cleanupCost k d) := by
  rw [input,ActivePrefixLayoutHeadersEndpoint.input_eq d hs hv hc]
  exact ActivePrefixDirtyControlHeadersRun.cleans k d

theorem outputs (mode : Kind) (d : Inputs) (j : Fin 10) :
    (bank (a := a) (finished mode d)).tape (Fin.castAdd 15 (Fin.natAdd 14 (Fin.castAdd 4 j)))=
      RadixZeroFill.encodedBinary (words mode d j) ∧
    (bank (a := a) (finished mode d)).head (Fin.castAdd 15 (Fin.natAdd 14 (Fin.castAdd 4 j)))=1 := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem originals_retained (mode : Kind) (d : Inputs) (hs : Fin 14 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 14) :
    (bank (a := a) (finished mode d)).head (Fin.castAdd 29 j)=(input (a := a) hs).head (Fin.castAdd 29 j) ∧
    (bank (a := a) (finished mode d)).tape (Fin.castAdd 29 j)=(input (a := a) hs).tape (Fin.castAdd 29 j) := by
  rw [input,ActivePrefixLayoutHeadersEndpoint.input_eq d hs hv hc]
  fin_cases j <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersEndpoint
