import IntegerMultBounds.Machine.ArbitraryWidthJoinedHeaders

/-! Paid cleanup of all six generated joined/padded headers. The original
P,G,B,e,rho,R' descriptors are retained literally and all six targets return
to wholly blank tapes with heads at zero. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersCleanup
noncomputable section
open ArbitraryWidthJoinedHeaders
open BinaryDescriptorCleanupList (cleared cleared_frame cleared_slot)
variable {a : ℕ}

def slots : List (Fin 12) := [6,7,8,9,10,11]
def program := BinaryDescriptorCleanupList.program (a := a) (by decide : 0 < 12) slots

def wordsAt (hs : Fin 6 → List Bool) (e r : ℕ) (i : Fin 12) :=
  if h : 6 ≤ i.val then words hs e r ⟨i.val-6,by omega⟩ else []

private theorem slots_nodup : slots.Nodup := by decide

private theorem descriptors (hs : Fin 6 → List Bool) (e r : ℕ)
    (i : Fin 12) (hi : i ∈ slots) :
    (output (a := a) hs e r).head i = 1 ∧
    (output (a := a) hs e r).tape i = BinaryDescriptorStack.descriptor (wordsAt hs e r i) := by
  simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first | rfl | exact encoded_descriptor _

private theorem cleared_eq (hs : Fin 6 → List Bool) (e r : ℕ) :
    cleared slots (output (a := a) hs e r) = ArbitraryWidthJoinedHeaders.input hs := by
  have hblank (i : Fin 12) (hi : i ∈ slots) :
      (ArbitraryWidthJoinedHeaders.input (a := a) hs).head i = 0 ∧
      (ArbitraryWidthJoinedHeaders.input (a := a) hs).tape i = fun _ => blank := by
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨rfl,rfl⟩
  have hframe (i : Fin 12) (hi : i ∉ slots) :
      (output (a := a) hs e r).head i = (ArbitraryWidthJoinedHeaders.input (a := a) hs).head i ∧
      (output (a := a) hs e r).tape i = (ArbitraryWidthJoinedHeaders.input (a := a) hs).tape i := by
    have hil : i.val < 6 := by fin_cases i <;> simp [slots] at hi ⊢
    simp [output,state,ArbitraryWidthJoinedHeaders.input,bank,hil]
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i ∈ slots
    · exact (cleared_slot slots slots_nodup (output hs e r) i hi).1.trans (hblank i hi).1.symm
    · exact (cleared_frame slots (output hs e r) i hi).1.trans (hframe i hi).1
  · funext i
    by_cases hi : i ∈ slots
    · exact (cleared_slot slots slots_nodup (output hs e r) i hi).2.trans (hblank i hi).2.symm
    · exact (cleared_frame slots (output hs e r) i hi).2.trans (hframe i hi).2

theorem cleans (hs : Fin 6 → List Bool) (e r : ℕ) :
    HoareTime (program (a := a)) (fun v => v = output hs e r)
      (fun v => v = ArbitraryWidthJoinedHeaders.input hs) (BinaryDescriptorCleanupList.cost slots (wordsAt hs e r)) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0 < 12)
    slots slots_nodup (wordsAt hs e r) (output hs e r) (descriptors hs e r)
  rw [cleared_eq] at h
  exact h

theorem cost_length (hs : Fin 6 → List Bool) (e r : ℕ) :
    BinaryDescriptorCleanupList.cost slots (wordsAt hs e r) =
      2*((hs 0).length+(hs 5).length+(RecursiveChildQuotientsConstant.bits 1).length+
        (RecursiveChildQuotientsConstant.bits (e-r)).length+(hs 1).length+(hs 2).length)+30 := by
  simp [BinaryDescriptorCleanupList.cost,slots,wordsAt,words]
  omega

theorem cost_linear (hs : Fin 6 → List Bool) (P G B e r R V : ℕ) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V) :
    BinaryDescriptorCleanupList.cost slots (wordsAt hs e r) ≤ 54*V := by
  have hh := headers hs P G B e r R hv hc
  have hwords (i : Fin 6) : Counter.value (words hs e r i) ≤ V := by
    rw [hh.1 i]
    fin_cases i
    · exact hP
    · exact hR
    · change 1 ≤ V; omega
    · change e-r ≤ V; omega
    · exact hG
    · exact hB
  have h := BinaryDescriptorCleanupList.cost_le slots (wordsAt hs e r) (V+1) (by
    intro i hi
    have hi' : 6 ≤ i.val := by fin_cases i <;> simp [slots] at hi ⊢
    let j : Fin 6 := ⟨i.val-6,by omega⟩
    change (if h : 6 ≤ i.val then words hs e r ⟨i.val-6,by omega⟩ else []).length ≤ V+1
    rw [dite_eq_left hi']
    exact (GrowingCounterData.canonical_width (words hs e r j) (hh.2 j)).trans
      ((Nat.add_le_add_right (Nat.log2_le_self _) 1).trans (Nat.add_le_add_right (hwords j) 1)))
  have hl : slots.length = 6 := rfl
  rw [hl] at h
  omega

theorem cleans_linear (hs : Fin 6 → List Bool) (P G B e r R V : ℕ) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V) :
    HoareTime (program (a := a)) (fun v => v = output hs e r)
      (fun v => v = ArbitraryWidthJoinedHeaders.input hs) (54*V) :=
  (cleans hs e r).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear hs P G B e r R V hV hv hc hP hG hB he hR)

end
end IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersCleanup
