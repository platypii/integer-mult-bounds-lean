import IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsShared
import IntegerMultBounds.Machine.ArbitraryWidthHighPaddingSuffix

/-! Copy original headers, construct high dimensions and suffix, and clean
all seventeen private tapes using actual programs. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsAndSuffixShared
noncomputable section
variable {a t : ℕ}
open ArbitraryWidthHighDimensions (dataVolume originalValues)

abbrev output (q P G B e r : ℕ) (hs : Fin 5 → List Bool) : Tapes 17 a :=
  ArbitraryWidthHighPaddingSuffix.output q P e r G B hs

def suffixProgram := Placement.placed (ArbitraryWidthHighPaddingSuffix.program (a := a))
  (finAddFlip : Fin (17+t) ≃ Fin (t+17))
def eraseSuffix := Placement.placed (ArbitraryWidthHighPaddingSuffix.cleanup (a := a))
  (finAddFlip : Fin (17+t) ≃ Fin (t+17))
def program (focus : Fin 5 → Fin t) (q : ℕ) :=
  seq (ArbitraryWidthHighDimensionsShared.program (a := a) focus q) suffixProgram
def cleanup := seq (eraseSuffix (a := a) (t := t))
  (ArbitraryWidthHighDimensionsShared.cleanup (a := a) (t := t))

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

theorem constructs (focus : Fin 5 → Fin t) (caller : Tapes t a)
    (q P G B e r : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus q)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 17))
      (fun z => z = caller.append (output q P G B e r hs))
      ((ArbitraryWidthHighDimensions.linearConstant q+133)*dataVolume q P G B e) := by
  have hd := ArbitraryWidthHighDimensionsShared.constructs focus caller q P G B e r hq hr hP hG hB hs hv hc ht hh
  have hsuf := right_hoare (ArbitraryWidthHighPaddingSuffix.constructs_linear (a := a)
    q P e r G B hq hG hB hs) caller
  have hV := (ArbitraryWidthHighDimensionsShared.original_bounds q P G B e r hq hr hP hG hB).1
  have hl := ArbitraryWidthHighPaddingSuffix.suffix_le_parent q P e r G B hq hr hP
  rw [ArbitraryWidthHighPaddingSuffix.original_volume] at hl
  apply (hd.seq hsuf).consequence (fun _ h => h) (fun _ h => h)
  nlinarith

theorem cleans (focus : Fin 5 → Fin t) (caller : Tapes t a)
    (q P G B e r : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t))
      (fun z => z = caller.append (output q P G B e r hs))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 17))
      (109*dataVolume q P G B e) := by
  have hsuf := right_hoare (ArbitraryWidthHighPaddingSuffix.cleans_linear (a := a)
    q P e r G B hq hG hB hs) caller
  have hd := ArbitraryWidthHighDimensionsShared.cleans focus caller q P G B e r hq hr hP hG hB hs hv hc
  have hV := (ArbitraryWidthHighDimensionsShared.original_bounds q P G B e r hq hr hP hG hB).1
  have hl := ArbitraryWidthHighPaddingSuffix.suffix_le_parent q P e r G B hq hr hP
  rw [ArbitraryWidthHighPaddingSuffix.original_volume] at hl
  apply (hsuf.seq hd).consequence (fun _ h => h) (fun _ h => h)
  omega

def headerWords (q P G B e r : ℕ) (hs : Fin 5 → List Bool) : Fin (5+6) → List Bool :=
  Fin.addCases hs (ArbitraryWidthHighDimensions.words q P G B e r)
def headerValues (q P G B e r : ℕ) : Fin (5+6) → ℕ :=
  Fin.addCases (originalValues P G B e r) (ArbitraryWidthHighDimensions.values q P G B e r)

theorem headers_value (q P G B e r : ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues P G B e r i) (i : Fin (5+6)) :
    Counter.value (headerWords q P G B e r hs i) = headerValues q P G B e r i := by
  unfold headerWords headerValues
  induction i using Fin.addCases with
  | left i => simpa only [Fin.addCases_left] using hv i
  | right i => simpa only [Fin.addCases_right] using ArbitraryWidthHighDimensions.words_value q P G B e r i

theorem headers_canonical (q P G B e r : ℕ) (hs : Fin 5 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (i : Fin (5+6)) :
    GrowingCounterData.Canonical (headerWords q P G B e r hs i) := by
  unfold headerWords
  induction i using Fin.addCases with
  | left i => simpa only [Fin.addCases_left] using hc i
  | right i => simpa only [Fin.addCases_right] using ArbitraryWidthHighDimensions.words_canonical q P G B e r i

theorem headers_cells (q P G B e r : ℕ) (hs : Fin 5 → List Bool) (i : Fin 11) :
    (output (a := a) q P G B e r hs).head (Fin.castAdd 6 i) = 1 ∧
    (output (a := a) q P G B e r hs).tape (Fin.castAdd 6 i) =
      RadixZeroFill.encodedBinary (headerWords q P G B e r hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem suffix_cells (q P G B e r : ℕ) (hs : Fin 5 → List Bool) :
    (output (a := a) q P G B e r hs).head 12 = 1 ∧
    (output (a := a) q P G B e r hs).tape 12 =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighPaddingSuffix.bits q e r G B) := by
  exact ⟨rfl,rfl⟩

theorem suffix_value (q e r G B : ℕ) :
    Counter.value (ArbitraryWidthHighPaddingSuffix.bits q e r G B) =
      ArbitraryWidthHighPaddingSuffix.rowLength q e r G B :=
  ArbitraryWidthHighPaddingSuffix.bits_value q e r G B

theorem suffix_canonical (q e r G B : ℕ) :
    GrowingCounterData.Canonical (ArbitraryWidthHighPaddingSuffix.bits q e r G B) :=
  ArbitraryWidthHighPaddingSuffix.bits_canonical q e r G B

theorem blank_remaining (q P G B e r : ℕ) (hs : Fin 5 → List Bool)
    (i : Fin 17) (hi : 11 ≤ i.val) (hne : i ≠ 12) :
    (output (a := a) q P G B e r hs).head i = 0 ∧
    (output (a := a) q P G B e r hs).tape i = fun _ => blank := by
  fin_cases i <;> first
  | exact ⟨rfl,rfl⟩
  | solve | norm_num at hi
  | exact (hne rfl).elim

end
end IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsAndSuffixShared
