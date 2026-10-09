import IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeaders

/-! Erase all six physically generated folded root headers while retaining
all original headers and restoring the exact original blank workspace. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersCleanup
noncomputable section
variable {a : ℕ}
open RecursiveInterchangeLayout (Descriptor)
open ArbitraryWidthHighFoldHeaders
open BinaryDescriptorCleanupList (cleared cleared_frame cleared_slot)

def slots : List (Fin 16) := [6,7,8,9,10,11]
def program := BinaryDescriptorCleanupList.program (a := a) (by decide : 0 < 16) slots
def wordsAt (v : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 16) :=
  if h : 6 ≤ i.val ∧ i.val < 12 then words v hs ⟨i.val-6,by omega⟩ else []
def cost (v : Descriptor) (hs : Fin 6 → List Bool) := BinaryDescriptorCleanupList.cost slots (wordsAt v hs)
private theorem slots_nodup : slots.Nodup := by decide

private theorem descriptors (v : Descriptor) (hs : Fin 6 → List Bool)
    (i : Fin 16) (hi : i ∈ slots) :
    (output (a := a) v hs).head i = 1 ∧
    (output (a := a) v hs).tape i = BinaryDescriptorStack.descriptor (wordsAt v hs i) := by
  simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem cleared_eq (v : Descriptor) (hs : Fin 6 → List Bool) :
    cleared slots (output (a := a) v hs) = ArbitraryWidthHighFoldHeaders.input hs := by
  have hblank (i : Fin 16) (hi : i ∈ slots) :
      (ArbitraryWidthHighFoldHeaders.input (a := a) hs).head i = 0 ∧ (ArbitraryWidthHighFoldHeaders.input (a := a) hs).tape i = fun _ => blank := by
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨rfl,rfl⟩
  have hframe (i : Fin 16) (hi : i ∉ slots) :
      (output (a := a) v hs).head i = (ArbitraryWidthHighFoldHeaders.input (a := a) hs).head i ∧
      (output (a := a) v hs).tape i = (ArbitraryWidthHighFoldHeaders.input (a := a) hs).tape i := by
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ | simp [slots] at hi
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i ∈ slots
    · exact (cleared_slot slots slots_nodup (output v hs) i hi).1.trans (hblank i hi).1.symm
    · exact (cleared_frame slots (output v hs) i hi).1.trans (hframe i hi).1
  · funext i
    by_cases hi : i ∈ slots
    · exact (cleared_slot slots slots_nodup (output v hs) i hi).2.trans (hblank i hi).2.symm
    · exact (cleared_frame slots (output v hs) i hi).2.trans (hframe i hi).2

theorem cleans (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (program (a := a)) (fun z => z = output v hs)
      (fun z => z = ArbitraryWidthHighFoldHeaders.input hs) (cost v hs) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0 < 16)
    slots slots_nodup (wordsAt v hs) (output v hs) (descriptors v hs)
  rw [cleared_eq] at h
  exact h

theorem cost_length (v : Descriptor) (hs : Fin 6 → List Bool) : cost v hs =
    2*((words v hs 0).length+(words v hs 1).length+(words v hs 2).length+
      (words v hs 3).length+(words v hs 4).length+(words v hs 5).length)+30 := by
  simp [cost,BinaryDescriptorCleanupList.cost,slots,wordsAt]
  omega

theorem cost_linear (v : Descriptor) (hs : Fin 6 → List Bool) (V : ℕ)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs)
    (hprefix : v.beforeRows*v.rows*v.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values v i ≤ V) : cost v hs ≤ 54*V := by
  have hV : 0 < V := lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1) hprefix
  have hw := headers v hs hh
  have hvalues (i : Fin 6) : Counter.value (words v hs i) ≤ V := by
    rw [hw.1 i]
    fin_cases i
    · exact hprefix
    · change 1 ≤ V; omega
    · change 1 ≤ V; omega
    · exact hv 3
    · exact hv 4
    · exact hv 5
  have hlength (i : Fin 6) : (words v hs i).length ≤ V+1 :=
    (GrowingCounterData.canonical_width _ (hw.2 i)).trans
      (Nat.add_le_add_right ((Nat.log2_le_self _).trans (hvalues i)) 1)
  rw [cost_length]
  have h0 := hlength 0
  have h1 := hlength 1
  have h2 := hlength 2
  have h3 := hlength 3
  have h4 := hlength 4
  have h5 := hlength 5
  omega

theorem cleans_linear (v : Descriptor) (hs : Fin 6 → List Bool) (V : ℕ)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs)
    (hprefix : v.beforeRows*v.rows*v.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values v i ≤ V) :
    HoareTime (program (a := a)) (fun z => z = output v hs)
      (fun z => z = ArbitraryWidthHighFoldHeaders.input hs) (54*V) :=
  (cleans v hs).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear v hs V hp hh hprefix hv)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersCleanup
