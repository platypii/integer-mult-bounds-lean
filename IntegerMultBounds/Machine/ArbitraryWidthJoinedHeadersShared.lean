import IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersCleanup
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! Physically wire the six retained sources into a blank private joined
header bank, generate all six target headers, then erase the entire bank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersShared
noncomputable section
variable {a t : ℕ}
open ArbitraryWidthJoinedHeaders (originalValues)

def destination : Fin 6 → Fin 12 := Fin.castAdd 6
private theorem destination_injective : Function.Injective destination := Fin.castAdd_injective _ _
def copyProgram (focus : Fin 6 → Fin t) := FixedHeaderSparseBankCopy.program
  (a := a) (by omega : 0 < t+6) focus destination destination_injective (by decide)
def joinedProgram := Placement.placed (ArbitraryWidthJoinedHeaders.program (a := a))
  (finAddFlip : Fin (12+t) ≃ Fin (t+12))
def program (focus : Fin 6 → Fin t) := seq (copyProgram (a := a) focus) joinedProgram

def eraseJoined := Placement.placed (ArbitraryWidthJoinedHeadersCleanup.program (a := a))
  (finAddFlip : Fin (12+t) ≃ Fin (t+12))
def eraseCopies := FixedHeaderSparseBankCopy.cleanup (a := a)
  (by omega : 0 < t+6) destination destination_injective (by decide)
def cleanup := seq (eraseJoined (a := a) (t := t)) eraseCopies

theorem input_bank (hs : Fin 6 → List Bool) :
    ArbitraryWidthJoinedHeaders.input (a := a) hs =
      FixedHeaderSparseBankCopy.headerBank destination hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective
  · intro i; fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro j hj
    have hhigh : 6 ≤ j.val := by
      by_contra h
      have hj' : j.val < 6 := by omega
      exact hj ⟨j.val,hj'⟩ (Fin.ext rfl)
    fin_cases j <;> first | exact ⟨rfl,rfl⟩ | norm_num at hhigh

private theorem right_hoare {states budget : ℕ} {M : Program 12 states a}
    {v w : Tapes 12 a} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget)
    (caller : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (12+t) ≃ Fin (t+12)))
      (fun z => z = caller.append v) (fun z => z = caller.append w) budget := by
  have ha : Placement.active (finAddFlip : Fin (12+t) ≃ Fin (t+12)) (caller.append v) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hw : Placement.active (finAddFlip : Fin (12+t) ≃ Fin (t+12)) (caller.append w) = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hf : Placement.extra (finAddFlip : Fin (12+t) ≃ Fin (t+12)) (caller.append v) =
      Placement.extra (finAddFlip : Fin (12+t) ≃ Fin (t+12)) (caller.append w) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hp := Placement.hoare_at h _ (caller.append v) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,hs,rfl⟩
  rw [hs,Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine
    (finAddFlip : Fin (12+t) ≃ Fin (t+12)) z
    (Placement.extra finAddFlip (caller.append w))) hw.symm).trans (Placement.view _ _)


theorem source_bounds (P G B e r R V : ℕ) (hr : r ≤ e)
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V) :
    ∀ i, originalValues P G B e r R i ≤ V := by
  intro i; fin_cases i
  all_goals first | exact hP | exact hG | exact hB | exact he | exact hR | exact hr.trans he

theorem constructs (focus : Fin 6 → Fin t) (caller : Tapes t a)
    (hs : Fin 6 → List Bool) (P G B e r R V : ℕ) (hr : r ≤ e) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 12))
      (fun z => z = caller.append (ArbitraryWidthJoinedHeaders.output hs e r)) (144*V) := by
  have hb := source_bounds P G B e r R V hr hP hG hB he hR
  have hcopy := FixedHeaderSparseBankCopy.constructs_linear (a := a)
    (by omega : 0 < t+6) focus destination destination_injective (by decide) caller hs ht hh
    V hV hc (by intro i; rw [hv]; exact hb i)
  rw [← input_bank] at hcopy
  have hd := right_hoare (ArbitraryWidthJoinedHeaders.constructs_values (a := a)
    hs P G B e r R V hr hV hv hc hP hG hB he hR) caller
  exact (hcopy.seq hd).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cleans (caller : Tapes t a) (hs : Fin 6 → List Bool)
    (P G B e r R V : ℕ) (hr : r ≤ e) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : P ≤ V) (hG : G ≤ V) (hB : B ≤ V) (he : e ≤ V) (hR : R ≤ V) :
    HoareTime (cleanup (a := a) (t := t))
      (fun z => z = caller.append (ArbitraryWidthJoinedHeaders.output hs e r))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 12)) (109*V) := by
  have hb := source_bounds P G B e r R V hr hP hG hB he hR
  have hd := right_hoare (ArbitraryWidthJoinedHeadersCleanup.cleans_linear (a := a)
    hs P G B e r R V hV hv hc hP hG hB he hR) caller
  have hcopy := FixedHeaderSparseBankCopy.cleans_linear (a := a)
    (by omega : 0 < t+6) destination destination_injective (by decide) caller hs
    V hV hc (by intro i; rw [hv]; exact hb i)
  rw [← input_bank] at hcopy
  exact (hd.seq hcopy).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The six actual targets satisfy the complete joined/padded root interface. -/
theorem headers (hs : Fin 6 → List Bool) (P G B e r R : ℕ)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r R i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    RecursiveDimensionBank.Headers (ArbitraryWidthJoinedHeaders.descriptor P G B e r R)
      (ArbitraryWidthJoinedHeaders.words hs e r) :=
  ArbitraryWidthJoinedHeaders.headers hs P G B e r R hv hc

end
end IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersShared
