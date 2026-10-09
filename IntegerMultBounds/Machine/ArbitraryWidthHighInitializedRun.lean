import IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitializeCleanup

/-! The high-width execution from wholly blank private banks: construct all
headers, run the actual high body, and erase every private header afterwards. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighInitializedRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor joinedDescriptor)
open ArbitraryWidthHighPrepare (highDepth rounded)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthExecutionPrivateHeadersCore
open ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open ArbitraryWidthExecutionPrivateHeadersPadding (paddedWords)
open ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open ArbitraryWidthHighExecutionInitialize (Sources Bounded)
variable {t : ℕ}

def program (focus : Fin t) (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t)
    (padding : Fin 10 → Fin t) :=
  seq (seq (ArbitraryWidthHighExecutionInitialize.program exchange movement padding)
    (ArbitraryWidthHighRun.program focus)) (ArbitraryWidthHighExecutionInitializeCleanup.program (t := t))

def cost (V P e G B : ℕ) (rh : Fin 6 → List Bool) : ℕ :=
  222*V+ArbitraryWidthHighCost.cost 0 P e G B rh+200*V+2

/-- No preinitialized execution banks or allocation oracle is assumed. The
copy source words reside on retained caller tapes; every private bank starts
and finishes blank, and the caller's sole changed tape is the exact transpose. -/
theorem runs (caller : Tapes t prime) (focus : Fin t)
    (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t) (padding : Fin 10 → Fin t)
    (P e G B V : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hV : 0 < V)
    (hfit : highDepth prime e ≤ e)
    (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hr : Counter.value rs = highDepth prime e)
    (hss : Counter.value ss = prime^(e-highDepth prime e)*G)
    (hop : Counter.value op = P*prime^(highDepth prime e))
    (hoe : Counter.value oe = prime^(e-highDepth prime e)*B)
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers
      (joinedDescriptor prime P e (highDepth prime e) G B) (rounded prime e) ph)
    (hroot : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) rh)
    (he : Sources caller exchange (exchangeWords hs rs))
    (hm : Sources caller movement (movementWords ss op oe rs))
    (hp : Sources caller padding (paddedWords ph rh))
    (be : Bounded (exchangeWords hs rs) V) (bm : Bounded (movementWords ss op oe rs) V)
    (bp : Bounded (paddedWords ph rh) V)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus exchange movement padding)
      (fun w => w = ArbitraryWidthHighExecutionInitialize.input caller)
      (fun w => w = ArbitraryWidthHighExecutionInitialize.input
        (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0))
      (cost V P e G B rh) := by
  have h1 := ArbitraryWidthHighExecutionInitialize.constructs caller exchange movement padding
    hs rs ss op oe ph rh V hV he hm hp be bm bp
  have h2 := ArbitraryWidthHighRun.runs caller focus P e G B hP hG hB hfit hs rs ss op oe hv
    hr (bm.canonical 4) hss (bm.canonical 0) hop (bm.canonical 1) hoe (bm.canonical 2)
    ph rh hpadding hroot blankTape 0 emptyOne emptyOne emptyTwo Shared50RecursiveRootExecution.blank_ready
    emptyOne (RecursiveViewFrame.free_empty rh) x hf hh
  have h3 := ArbitraryWidthHighExecutionInitializeCleanup.cleans
    (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    hs rs ss op oe ph rh V hV be bm bp
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

def coefficient (D : ℕ) : ℝ := ArbitraryWidthHighCost.coefficient 0+(424*D : ℕ)

theorem coefficient_positive (D : ℕ) : 0 < coefficient D := by
  have h := ArbitraryWidthHighCost.coefficient_positive 0
  unfold coefficient
  positivity

/-- Any fixed domination of the metadata-word bound by original volume
absorbs physical setup, cleanup and sequence joins in the same exponent. -/
theorem cost_bound (V D P e G B : ℕ) (rh : Fin 6 → List Bool)
    (hV : 0 < V) (hdom : V ≤ D*volume prime (originalDescriptor P e G B))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (hroot : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) rh) :
    (cost V P e G B rh : ℝ) ≤ coefficient D*
      (volume prime (originalDescriptor P e G B) : ℝ)*(e : ℝ)^Parameters.tau := by
  have hbody := ArbitraryWidthHighRun.cost_bound P e G B rh hP hG hB hr hroot
  have hdom' : (V : ℝ) ≤ (D : ℝ)*(volume prime (originalDescriptor P e G B) : ℝ) := by
    exact_mod_cast hdom
  have hV' : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have he : 0 < e := by omega
  have hpower : 1 ≤ (e : ℝ)^Parameters.tau := Real.one_le_rpow (by exact_mod_cast he)
    Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlinear := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ (424 : ℝ)*(D : ℝ)*(volume prime (originalDescriptor P e G B) : ℝ) by positivity)
  unfold cost coefficient
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hbody,hdom',hV',hlinear]

/-- The common high-width metadata bound is twice the original volume;
its complete initialization/erasure contributes only the fixed coefficient848. -/
theorem cost_bound_twice (P e G B : ℕ) (rh : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (hroot : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) rh) :
    (cost (2*volume prime (originalDescriptor P e G B)) P e G B rh : ℝ) ≤ coefficient 2*
      (volume prime (originalDescriptor P e G B) : ℝ)*(e : ℝ)^Parameters.tau := by
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,(by change 0 < 1; decide),(by change 0 < 1; decide),hG,hB⟩
  have hvol := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le _ hp
  exact cost_bound _ 2 P e G B rh (by omega) le_rfl hP hG hB hr hroot

end
end IntegerMultBounds.Machine.ArbitraryWidthHighInitializedRun
