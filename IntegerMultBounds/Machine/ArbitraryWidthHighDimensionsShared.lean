import IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsCleanup
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! Copy the five original dimension sources from a caller, construct the
actual high-layout dimensions, then erase both generated and copied headers. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsShared
noncomputable section
variable {a t : ℕ}
open ArbitraryWidthHighDimensions (dataVolume originalValues)

def destination : Fin 5 → Fin 17 := Fin.castAdd 12
private theorem destination_injective : Function.Injective destination := Fin.castAdd_injective _ _

def copyProgram (focus : Fin 5 → Fin t) := FixedHeaderSparseBankCopy.program
  (a := a) (by omega : 0 < t+5) focus destination destination_injective (by decide)
def dimensionProgram (q : ℕ) := Placement.placed (ArbitraryWidthHighDimensions.program (a := a) q)
  (finAddFlip : Fin (17+t) ≃ Fin (t+17))
def program (focus : Fin 5 → Fin t) (q : ℕ) := seq (copyProgram (a := a) focus) (dimensionProgram q)
def eraseDimensions := Placement.placed (ArbitraryWidthHighDimensionsCleanup.program (a := a))
  (finAddFlip : Fin (17+t) ≃ Fin (t+17))
def eraseCopies := FixedHeaderSparseBankCopy.cleanup (a := a)
  (by omega : 0 < t+5) destination destination_injective (by decide)
def cleanup := seq (eraseDimensions (a := a) (t := t)) eraseCopies

theorem input_bank (hs : Fin 5 → List Bool) :
    ArbitraryWidthHighDimensions.input (a := a) hs =
      FixedHeaderSparseBankCopy.headerBank destination hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective
  · intro i; fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro j hj
    have hhigh : 5 ≤ j.val := by
      by_contra h
      have hj' : j.val < 5 := by omega
      exact hj ⟨j.val,hj'⟩ (Fin.ext rfl)
    fin_cases j <;> first | exact ⟨rfl,rfl⟩ | norm_num at hhigh

private theorem right_hoare {states budget : ℕ} {M : Program 17 states a}
    {v w : Tapes 17 a} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget)
    (caller : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (17+t) ≃ Fin (t+17)))
      (fun z => z = caller.append v) (fun z => z = caller.append w) budget := by
  have ha : Placement.active (finAddFlip : Fin (17+t) ≃ Fin (t+17)) (caller.append v) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hw : Placement.active (finAddFlip : Fin (17+t) ≃ Fin (t+17)) (caller.append w) = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hf : Placement.extra (finAddFlip : Fin (17+t) ≃ Fin (t+17)) (caller.append v) =
      Placement.extra (finAddFlip : Fin (17+t) ≃ Fin (t+17)) (caller.append w) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hp := Placement.hoare_at h _ (caller.append v) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,hs,rfl⟩
  rw [hs,Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine
    (finAddFlip : Fin (17+t) ≃ Fin (t+17)) z
    (Placement.extra finAddFlip (caller.append w))) hw.symm).trans (Placement.view _ _)

theorem original_bounds (q P G B e r : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    0 < dataVolume q P G B e ∧ ∀ i, originalValues P G B e r i ≤ dataVolume q P G B e := by
  obtain ⟨hV,he,hvalues⟩ := ArbitraryWidthHighDimensions.data_volume_bounds q P G B e r hq hr hP hG hB
  have hpow : 0 < q^r := pow_pos (by omega) _
  have hlow : 0 < q^(e-r) := pow_pos (by omega) _
  have hp := (Nat.le_mul_of_pos_right P hpow).trans (hvalues 3)
  have hg := (Nat.le_mul_of_pos_right G hlow).trans (hvalues 4)
  have hb := (Nat.le_mul_of_pos_right B hlow).trans (hvalues 5)
  refine ⟨hV,?_⟩
  intro i; fin_cases i
  · exact hp
  · exact hg
  · exact hb
  · exact he
  · change r ≤ _; omega

theorem constructs (focus : Fin 5 → Fin t) (caller : Tapes t a)
    (q P G B e r : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus q)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 17))
      (fun z => z = caller.append (ArbitraryWidthHighDimensions.output q P G B e r hs))
      ((ArbitraryWidthHighDimensions.linearConstant q+51)*dataVolume q P G B e) := by
  obtain ⟨hV,hvalues⟩ := original_bounds q P G B e r hq hr hP hG hB
  have hcopy := FixedHeaderSparseBankCopy.constructs_linear (a := a)
    (by omega : 0 < t+5) focus destination destination_injective (by decide) caller hs ht hh
    (dataVolume q P G B e) hV hc (by intro i; rw [hv]; exact hvalues i)
  rw [← input_bank] at hcopy
  have hd := right_hoare (ArbitraryWidthHighDimensions.construct_linear (a := a)
    q P G B e r hq hr hP hG hB hs hv hc) caller
  apply (hcopy.seq hd).consequence (fun _ h => h) (fun _ h => h)
  nlinarith

theorem cleans (_focus : Fin 5 → Fin t) (caller : Tapes t a)
    (q P G B e r : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t))
      (fun z => z = caller.append (ArbitraryWidthHighDimensions.output q P G B e r hs))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 17))
      (100*dataVolume q P G B e) := by
  obtain ⟨hV,hvalues⟩ := original_bounds q P G B e r hq hr hP hG hB
  have hd := right_hoare (ArbitraryWidthHighDimensionsCleanup.cleans_linear (a := a)
    q P G B e r hs hq hr hP hG hB) caller
  have hcopy := FixedHeaderSparseBankCopy.cleans_linear (a := a)
    (by omega : 0 < t+5) destination destination_injective (by decide) caller hs
    (dataVolume q P G B e) hV hc (by intro i; rw [hv]; exact hvalues i)
  rw [← input_bank] at hcopy
  apply (hd.seq hcopy).consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsShared
