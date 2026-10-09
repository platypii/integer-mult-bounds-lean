import IntegerMultBounds.Machine.ArbitraryWidthHighDimensions
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Actual erasure of all six generated high-layout descriptors retains the
sole original headers and restores every private tape to blank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsCleanup
noncomputable section
open ArbitraryWidthHighDimensions
open BinaryDescriptorCleanupList (cleared cleared_frame cleared_slot)
variable {a : ℕ}

def slots : List (Fin 17) := [5,6,7,8,9,10]
def program := BinaryDescriptorCleanupList.program (a := a) (by decide : 0 < 17) slots

def wordsAt (q P G B e r : ℕ) (i : Fin 17) :=
  if h : 5 ≤ i.val ∧ i.val < 11 then words q P G B e r ⟨i.val-5,by omega⟩ else []

private theorem slots_nodup : slots.Nodup := by decide

private theorem descriptors (q P G B e r : ℕ) (hs : Fin 5 → List Bool)
    (i : Fin 17) (hi : i ∈ slots) :
    (output (a := a) q P G B e r hs).head i = 1 ∧
    (output (a := a) q P G B e r hs).tape i = BinaryDescriptorStack.descriptor (wordsAt q P G B e r i) := by
  fin_cases i
  all_goals first | (simp [slots] at hi; done) |
    (constructor
     · rfl
     · change RadixZeroFill.encodedBinary _ = BinaryDescriptorStack.descriptor _
       exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)

private theorem cleared_eq (q P G B e r : ℕ) (hs : Fin 5 → List Bool) :
    cleared slots (output (a := a) q P G B e r hs) = ArbitraryWidthHighDimensions.input (a := a) hs := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (cleared slots (output (a := a) q P G B e r hs)).head i = (ArbitraryWidthHighDimensions.input (a := a) hs).head i
    by_cases hi : i ∈ slots
    · rw [(cleared_slot slots slots_nodup _ i hi).1]
      fin_cases i <;> first | (simp [slots] at hi; done) | rfl
    · rw [(cleared_frame slots _ i hi).1]
      fin_cases i <;> first | (simp [slots] at hi; done) | rfl
  · funext i
    change (cleared slots (output (a := a) q P G B e r hs)).tape i = (ArbitraryWidthHighDimensions.input (a := a) hs).tape i
    by_cases hi : i ∈ slots
    · rw [(cleared_slot slots slots_nodup _ i hi).2]
      fin_cases i <;> first | (simp [slots] at hi; done) | rfl
    · rw [(cleared_frame slots _ i hi).2]
      fin_cases i <;> first | (simp [slots] at hi; done) | rfl

theorem cleans (q P G B e r : ℕ) (hs : Fin 5 → List Bool) :
    HoareTime (program (a := a)) (fun v => v = output q P G B e r hs)
      (fun v => v = ArbitraryWidthHighDimensions.input (a := a) hs) (BinaryDescriptorCleanupList.cost slots (wordsAt q P G B e r)) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0 < 17)
    slots slots_nodup (wordsAt q P G B e r) (output q P G B e r hs)
    (descriptors q P G B e r hs)
  rw [cleared_eq] at h
  exact h

theorem cost_le (q P G B e r V : ℕ) (hV : 0 < V)
    (hv : ∀ i, values q P G B e r i ≤ V) :
    BinaryDescriptorCleanupList.cost slots (wordsAt q P G B e r) ≤ 54*V := by
  have h := BinaryDescriptorCleanupList.cost_le slots (wordsAt q P G B e r) (V+1) (by
    intro i hi
    have hi' : 5 ≤ i.val ∧ i.val < 11 := by
      fin_cases i <;> simp [slots] at hi ⊢
    let j : Fin 6 := ⟨i.val-5,by omega⟩
    change (if h : 5 ≤ i.val ∧ i.val < 11 then words q P G B e r ⟨i.val-5,by omega⟩ else []).length ≤ V+1
    rw [dite_eq_left hi']
    have hc := GrowingCounterData.canonical_width (words q P G B e r j) (words_canonical q P G B e r j)
    rw [words_value] at hc
    exact hc.trans (by have := (Nat.log2_le_self (values q P G B e r j)).trans (hv j); omega))
  have hl : slots.length = 6 := rfl
  rw [hl] at h
  omega

theorem cleans_linear (q P G B e r : ℕ) (hs : Fin 5 → List Bool)
    (hq : 2 ≤ q) (hr : r ≤ e) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    HoareTime (program (a := a)) (fun v => v = output q P G B e r hs)
      (fun v => v = ArbitraryWidthHighDimensions.input (a := a) hs) (54*dataVolume q P G B e) := by
  obtain ⟨hV,_,hv⟩ := data_volume_bounds q P G B e r hq hr hP hG hB
  exact (cleans q P G B e r hs).consequence (fun _ h => h) (fun _ h => h)
    (cost_le q P G B e r _ hV hv)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsCleanup
