import IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsAndSuffixShared
import IntegerMultBounds.Machine.ArbitraryWidthJoinedHeadersShared
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
import IntegerMultBounds.Machine.ArbitraryWidthHighPaddedBudget

/-! Physically prepare all high-branch arithmetic, joined-root and zero-clock
banks from retained caller sources, then erase them in reverse order. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighBranchPrepare
noncomputable section
variable {a t : ℕ}
open ArbitraryWidthHighDimensions (dataVolume)

def input (base : Tapes t a) :=
  ((base.append (FixedHeaderBankCopy.empty 17)).append (FixedHeaderBankCopy.empty 12)).append
    ArbitraryWidthZeroHeaderShared.empty

def output (base : Tapes t a) (q P G B e r : ℕ) (hs : Fin 5 → List Bool) (js : Fin 6 → List Bool) :=
  ((base.append (ArbitraryWidthHighDimensionsAndSuffixShared.output q P G B e r hs)).append
    (ArbitraryWidthJoinedHeaders.output js e r)).append ArbitraryWidthZeroHeaderShared.header

def joinedFocus (focus : Fin 6 → Fin t) : Fin 6 → Fin (t+17) :=
  fun i => Fin.castAdd 17 (focus i)
def program (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t) (q : ℕ) :=
  seq (seq (extend (extend (ArbitraryWidthHighDimensionsAndSuffixShared.program (a := a) dimensions q) 12) 1)
    (extend (ArbitraryWidthJoinedHeadersShared.program (joinedFocus joined)) 1))
    ArbitraryWidthZeroHeaderShared.program

def cleanup := seq (seq (ArbitraryWidthZeroHeaderShared.cleanup (a := a) (t := (t+17)+12))
    (extend (ArbitraryWidthJoinedHeadersShared.cleanup (a := a) (t := t+17)) 1))
    (extend (extend (ArbitraryWidthHighDimensionsAndSuffixShared.cleanup (a := a) (t := t)) 12) 1)

def setupCost (q P G B e V : ℕ) :=
  (ArbitraryWidthHighDimensions.linearConstant q+133)*dataVolume q P G B e+144*V+8
def cleanupCost (q P G B e V : ℕ) := 109*dataVolume q P G B e+109*V+6

theorem constructs (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t) (base : Tapes t a)
    (q P G B e r R V : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hV : 0 < V)
    (hs : Fin 5 → List Bool) (js : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = ArbitraryWidthHighDimensions.originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (jv : ∀ i, Counter.value (js i) = ArbitraryWidthJoinedHeaders.originalValues P G B e r R i)
    (jc : ∀ i, GrowingCounterData.Canonical (js i))
    (bP : P ≤ V) (bG : G ≤ V) (bB : B ≤ V) (be : e ≤ V) (bR : R ≤ V)
    (ht : ∀ i, base.tape (dimensions i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, base.head (dimensions i) = 1)
    (jt : ∀ i, base.tape (joined i) = RadixZeroFill.encodedBinary (js i))
    (jh : ∀ i, base.head (joined i) = 1) :
    HoareTime (program dimensions joined q) (fun z => z = input base)
      (fun z => z = output base q P G B e r hs js) (setupCost q P G B e V) := by
  have hd := ArbitraryWidthHighDimensionsAndSuffixShared.constructs dimensions base q P G B e r
    hq hr hP hG hB hs hv hc ht hh
  have hd' := hoare_extend_eq (hoare_extend_eq hd (FixedHeaderBankCopy.empty 12))
    ArbitraryWidthZeroHeaderShared.empty
  let bd := base.append (ArbitraryWidthHighDimensionsAndSuffixShared.output q P G B e r hs)
  have hj := ArbitraryWidthJoinedHeadersShared.constructs (joinedFocus joined) bd js P G B e r R V
    hr hV jv jc bP bG bB be bR
    (by intro i; simpa only [bd,joinedFocus,Tapes.append,Fin.addCases_left] using jt i)
    (by intro i; simpa only [bd,joinedFocus,Tapes.append,Fin.addCases_left] using jh i)
  have hj' := hoare_extend_eq hj ArbitraryWidthZeroHeaderShared.empty
  have hz := ArbitraryWidthZeroHeaderShared.constructs
    (bd.append (ArbitraryWidthJoinedHeaders.output js e r))
  exact ((hd'.seq hj').seq hz).consequence (fun _ h => h) (fun _ h => h) (by
    unfold setupCost
    omega)

theorem cleans (dimensions : Fin 5 → Fin t) (base : Tapes t a)
    (q P G B e r R V : ℕ) (hq : 2 ≤ q) (hr : r ≤ e)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hV : 0 < V)
    (hs : Fin 5 → List Bool) (js : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = ArbitraryWidthHighDimensions.originalValues P G B e r i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (jv : ∀ i, Counter.value (js i) = ArbitraryWidthJoinedHeaders.originalValues P G B e r R i)
    (jc : ∀ i, GrowingCounterData.Canonical (js i))
    (bP : P ≤ V) (bG : G ≤ V) (bB : B ≤ V) (be : e ≤ V) (bR : R ≤ V) :
    HoareTime (cleanup (a := a) (t := t))
      (fun z => z = output base q P G B e r hs js) (fun z => z = input base)
      (cleanupCost q P G B e V) := by
  let bd := base.append (ArbitraryWidthHighDimensionsAndSuffixShared.output q P G B e r hs)
  have hz := ArbitraryWidthZeroHeaderShared.cleans
    (bd.append (ArbitraryWidthJoinedHeaders.output js e r))
  have hj := ArbitraryWidthJoinedHeadersShared.cleans bd js P G B e r R V hr hV jv jc bP bG bB be bR
  have hj' := hoare_extend_eq hj ArbitraryWidthZeroHeaderShared.empty
  have hd := ArbitraryWidthHighDimensionsAndSuffixShared.cleans dimensions base q P G B e r
    hq hr hP hG hB hs hv hc
  have hd' := hoare_extend_eq (hoare_extend_eq hd (FixedHeaderBankCopy.empty 12))
    ArbitraryWidthZeroHeaderShared.empty
  exact ((hz.seq hj').seq hd').consequence (fun _ h => h) (fun _ h => h) (by
    unfold cleanupCost
    omega)

/-- The actual rounded row source is bounded by twice the original volume;
the other original fields have the stronger original-volume bound. -/
theorem joined_source_bounds (P e G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hr : ArbitraryWidthHighPrepare.highDepth Networks.Shared50ModularControl.prime e ≤ e) :
    ∀ i, ArbitraryWidthJoinedHeaders.originalValues P G B e
      (ArbitraryWidthHighPrepare.highDepth Networks.Shared50ModularControl.prime e)
      (ArbitraryWidthHighPrepare.rounded Networks.Shared50ModularControl.prime e) i ≤
      2*dataVolume Networks.Shared50ModularControl.prime P G B e := by
  let q := Networks.Shared50ModularControl.prime
  let r := ArbitraryWidthHighPrepare.highDepth q e
  have ho := ArbitraryWidthHighDimensionsShared.original_bounds q P G B e r
    Networks.Shared50ModularControl.prime_prime.two_le hr hP hG hB
  have hpad := ArbitraryWidthHighPaddedBudget.positive P e G B hP hG hB
  have hrows := RecursiveHeaderBounds.values_le_volume Networks.Shared50ModularControl.prime_prime.two_le
    (ArbitraryWidthHighPaddedBudget.descriptor P e G B) hpad 1
  have hvol := ArbitraryWidthHighPaddedBudget.volume_le P e G B hr
  rw [ArbitraryWidthHighPaddingSuffix.original_volume] at hvol
  have hR : ArbitraryWidthHighPrepare.rounded q e ≤ 2*dataVolume q P G B e := hrows.trans hvol
  intro i; fin_cases i
  · have h := ho.2 0; change P ≤ _ at h; change P ≤ _; exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · have h := ho.2 1; change G ≤ _ at h; change G ≤ _; exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · have h := ho.2 2; change B ≤ _ at h; change B ≤ _; exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · have h := ho.2 3; change e ≤ _ at h; change e ≤ _; exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · have h := ho.2 4; change r ≤ _ at h; change r ≤ _; exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · exact hR

theorem setup_cost_bound (q P G B e : ℕ) (hV : 0 < dataVolume q P G B e) :
    setupCost q P G B e (2*dataVolume q P G B e) ≤
      (ArbitraryWidthHighDimensions.linearConstant q+429)*dataVolume q P G B e := by
  unfold setupCost
  nlinarith

theorem cleanup_cost_bound (q P G B e : ℕ) (hV : 0 < dataVolume q P G B e) :
    cleanupCost q P G B e (2*dataVolume q P G B e) ≤ 333*dataVolume q P G B e := by
  unfold cleanupCost
  omega

end
end IntegerMultBounds.Machine.ArbitraryWidthHighBranchPrepare
