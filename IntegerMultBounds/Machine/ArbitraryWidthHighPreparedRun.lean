import IntegerMultBounds.Machine.ArbitraryWidthHighBranchPrepare
import IntegerMultBounds.Machine.ArbitraryWidthHighRuntimeHeaderWiring
import IntegerMultBounds.Machine.ArbitraryWidthHighHeaderBounds

/-! Complete high execution with physical metadata preparation and erasure.
All metadata and execution banks start and finish wholly blank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPreparedRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor)
open ArbitraryWidthHighPrepare (highDepth rounded)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighRuntimeHeaderWiring
open ArbitraryWidthHighExecutionInitialize (Sources)
open ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
variable {t : ℕ}

def input (base : Tapes t prime) :=
  ArbitraryWidthHighExecutionInitialize.input (ArbitraryWidthHighBranchPrepare.input base)

def program (focus : Fin t) (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t)
    (exchange : Fin 7 → Fin t) (rows rounded : Fin t) :=
  seq (seq (extend (extend (extend
    (ArbitraryWidthHighBranchPrepare.program (a := prime) dimensions joined prime)
    ArbitraryWidthHighExchangeJoin.exchangeCount) ArbitraryWidthHighExchangeJoin.movementCount)
    ArbitraryWidthHighRun.paddingCount)
    (ArbitraryWidthHighInitializedRun.program (baseSlot focus) (exchangeFocus exchange)
      (movementFocus exchange) (paddingFocus rows rounded)))
    (extend (extend (extend (ArbitraryWidthHighBranchPrepare.cleanup (a := prime) (t := t))
      ArbitraryWidthHighExchangeJoin.exchangeCount) ArbitraryWidthHighExchangeJoin.movementCount)
      ArbitraryWidthHighRun.paddingCount)

def cost (P e G B : ℕ) (jh : Fin 6 → List Bool) :=
  ArbitraryWidthHighBranchPrepare.setupCost prime P G B e
      (2*volume prime (originalDescriptor P e G B))+1+
    ArbitraryWidthHighInitializedRun.cost (2*volume prime (originalDescriptor P e G B))
      P e G B (ArbitraryWidthJoinedHeaders.words jh e (highDepth prime e))+1+
    ArbitraryWidthHighBranchPrepare.cleanupCost prime P G B e
      (2*volume prime (originalDescriptor P e G B))

private theorem changed_bank (base : Tapes t prime) (focus : Fin t)
    (P G B e r : ℕ) (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool)
    (word : ℤ → Fin (prime+4)) :
    setTape (bank base P G B e r dh jh) (baseSlot focus) word 0 =
      bank (setTape base focus word 0) P G B e r dh jh := by
  unfold bank baseSlot
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]

theorem runs (base : Tapes t prime) (focus : Fin t)
    (dimensions : Fin 5 → Fin t) (joined : Fin 6 → Fin t) (exchange : Fin 7 → Fin t)
    (rowsSlot roundedSlot : Fin t) (P e G B : ℕ)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hfit : highDepth prime e ≤ e)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (hs : Fin 6 → List Bool)
    (rs rowBits roundedBits : List Bool)
    (dhv : ∀ i, Counter.value (dh i) =
      ArbitraryWidthHighDimensions.originalValues P G B e (highDepth prime e) i)
    (dhc : ∀ i, GrowingCounterData.Canonical (dh i))
    (jhv : ∀ i, Counter.value (jh i) = ArbitraryWidthJoinedHeaders.originalValues P G B e
      (highDepth prime e) (rounded prime e) i)
    (jhc : ∀ i, GrowingCounterData.Canonical (jh i))
    (sd : Sources base dimensions dh) (sj : Sources base joined jh)
    (he : Sources base exchange (exchangeWords hs rs))
    (hh : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hr : Counter.value rs = highDepth prime e) (cr : GrowingCounterData.Canonical rs)
    (hrows : Counter.value rowBits = prime^(2*highDepth prime e))
    (crows : GrowingCounterData.Canonical rowBits)
    (hrounded : Counter.value roundedBits = rounded prime e)
    (crounded : GrowingCounterData.Canonical roundedBits)
    (rowsTape : base.tape rowsSlot = RadixZeroFill.encodedBinary rowBits) (rowsHead : base.head rowsSlot = 1)
    (roundedTape : base.tape roundedSlot = RadixZeroFill.encodedBinary roundedBits)
    (roundedHead : base.head roundedSlot = 1)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : base.tape focus = sourceWord x) (hhead : base.head focus = 0) :
    HoareTime (program focus dimensions joined exchange rowsSlot roundedSlot)
      (fun z => z = input base)
      (fun z => z = input (setTape base focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) (cost P e G B jh) := by
  let r := highDepth prime e
  let V := 2*volume prime (originalDescriptor P e G B)
  have hdvol := ArbitraryWidthHighPaddingSuffix.original_volume prime P e G B
  have hpos := (ArbitraryWidthHighDimensionsShared.original_bounds prime P G B e r
    Shared50ModularControl.prime_prime.two_le hfit hP hG hB).1
  have hV : 0 < V := by dsimp only [V]; rw [hdvol]; omega
  have hb := ArbitraryWidthHighBranchPrepare.joined_source_bounds P e G B hP hG hB hfit
  rw [← hdvol] at hb
  have bP : P ≤ V := hb 0
  have bG : G ≤ V := hb 1
  have bB : B ≤ V := hb 2
  have be : e ≤ V := hb 3
  have bR : rounded prime e ≤ V := hb 5
  have hp := ArbitraryWidthHighBranchPrepare.constructs dimensions joined base
    prime P G B e r (rounded prime e) V Shared50ModularControl.prime_prime.two_le hfit
    hP hG hB hV dh jh dhv dhc jhv jhc bP bG bB be bR sd.tape sd.head sj.tape sj.head
  have hp' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hp
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime))
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime))
    (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
  let caller := bank base P G B e r dh jh
  let ss := ArbitraryWidthHighDimensions.words prime P G B e r 4
  let op := ArbitraryWidthHighDimensions.words prime P G B e r 3
  let oe := ArbitraryWidthHighDimensions.words prime P G B e r 5
  let ph := paddingWords dh rowBits roundedBits e r G B
  let rh := ArbitraryWidthJoinedHeaders.words jh e r
  have mv := movement_values P G B e r rs hr
  have mc := movement_canonical P G B e r rs cr
  have hss : Counter.value ss = prime^(e-r)*G := mv 0
  have hop : Counter.value op = P*prime^r := mv 1
  have hoe : Counter.value oe = prime^(e-r)*B := mv 2
  have css : GrowingCounterData.Canonical ss := mc 0
  have cop : GrowingCounterData.Canonical op := mc 1
  have coe : GrowingCounterData.Canonical oe := mc 2
  have hph := padding_headers P G B e r (rounded prime e) dh rowBits roundedBits
    (dhv 0) hrows hrounded (dhc 0) crows crounded
  have hrh := lowroot_headers P G B e r (rounded prime e) jh jhv jhc
  have bex := ArbitraryWidthHighHeaderBounds.exchange_bounded P e G B r hP hG hB hfit hs rs hh hr cr
  have bmv := ArbitraryWidthHighHeaderBounds.movement_bounded P e G B r hP hG hB hfit
    ss op oe rs hss css hop cop hoe coe hr cr
  have bpd := ArbitraryWidthHighHeaderBounds.padded_bounded P e G B hP hG hB hfit ph rh hph hrh
  have hbody := ArbitraryWidthHighInitializedRun.runs caller (baseSlot focus)
    (exchangeFocus exchange) (movementFocus exchange) (paddingFocus rowsSlot roundedSlot)
    P e G B V hP hG hB hV hfit hs rs ss op oe ph rh hh hr hss hop hoe hph hrh
    (exchange_sources base P G B e r dh jh exchange hs rs he)
    (movement_sources base P G B e r dh jh exchange hs rs he)
    (padding_sources base P G B e r dh jh rowsSlot roundedSlot rowBits roundedBits
      rowsTape rowsHead roundedTape roundedHead) bex bmv bpd x
    ((base_cells base P G B e r dh jh focus).2.trans hf)
    ((base_cells base P G B e r dh jh focus).1.trans hhead)
  rw [changed_bank] at hbody
  let changed := setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0
  have hc := ArbitraryWidthHighBranchPrepare.cleans dimensions changed
    prime P G B e r (rounded prime e) V Shared50ModularControl.prime_prime.two_le hfit
    hP hG hB hV dh jh dhv dhc jhv jhc bP bG bB be bR
  have hc' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hc
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime))
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime))
    (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
  exact ((hp'.seq hbody).seq hc').consequence (fun _ h => h) (fun _ h => h) (by
    unfold cost
    rfl)

def overheadCoefficient : ℕ := ArbitraryWidthHighDimensions.linearConstant prime+764
def coefficient : ℝ := ArbitraryWidthHighInitializedRun.coefficient 2+(overheadCoefficient : ℝ)

theorem coefficient_positive : 0 < coefficient := by
  have h := ArbitraryWidthHighInitializedRun.coefficient_positive 2
  unfold coefficient
  positivity

theorem overhead_bound (P e G B : ℕ)
    (hV : 0 < volume prime (originalDescriptor P e G B)) :
    ArbitraryWidthHighBranchPrepare.setupCost prime P G B e
        (2*volume prime (originalDescriptor P e G B))+
      ArbitraryWidthHighBranchPrepare.cleanupCost prime P G B e
        (2*volume prime (originalDescriptor P e G B))+2 ≤
      overheadCoefficient*volume prime (originalDescriptor P e G B) := by
  rw [ArbitraryWidthHighPaddingSuffix.original_volume] at hV ⊢
  have hs := ArbitraryWidthHighBranchPrepare.setup_cost_bound prime P G B e hV
  have hc := ArbitraryWidthHighBranchPrepare.cleanup_cost_bound prime P G B e hV
  unfold overheadCoefficient
  nlinarith

/-- The physically prepared high branch retains the same certified exponent;
all descriptor synthesis, copying, cleanup and outer sequence joins are paid. -/
theorem cost_bound (P e G B : ℕ) (jh : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (jhv : ∀ i, Counter.value (jh i) = ArbitraryWidthJoinedHeaders.originalValues P G B e
      (highDepth prime e) (rounded prime e) i)
    (jhc : ∀ i, GrowingCounterData.Canonical (jh i)) :
    (cost P e G B jh : ℝ) ≤ coefficient*
      (volume prime (originalDescriptor P e G B) : ℝ)*(e : ℝ)^Parameters.tau := by
  have hh := lowroot_headers P G B e (highDepth prime e) (rounded prime e) jh jhv jhc
  have hb := ArbitraryWidthHighInitializedRun.cost_bound_twice P e G B
    (ArbitraryWidthJoinedHeaders.words jh e (highDepth prime e)) hP hG hB hr hh
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le _ hp
  have ho := overhead_bound P e G B hV
  have hor : (ArbitraryWidthHighBranchPrepare.setupCost prime P G B e
        (2*volume prime (originalDescriptor P e G B)) : ℝ)+
      (ArbitraryWidthHighBranchPrepare.cleanupCost prime P G B e
        (2*volume prime (originalDescriptor P e G B)) : ℝ)+2 ≤
      (overheadCoefficient : ℝ)*(volume prime (originalDescriptor P e G B) : ℝ) := by
    exact_mod_cast ho
  have he : 0 < e := by omega
  have hpower : 1 ≤ (e : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast he) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlin := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ (overheadCoefficient : ℝ)*(volume prime (originalDescriptor P e G B) : ℝ) by positivity)
  unfold cost coefficient
  simp only [Nat.cast_add,Nat.cast_one]
  nlinarith only [hb,hor,hlin]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighPreparedRun
