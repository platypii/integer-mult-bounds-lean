module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPreparedRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighInitializedRunWithin

/-! Complete high execution with physical metadata preparation and erasure.
All metadata and execution banks start and finish wholly blank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPreparedRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPrepare (highDepth rounded)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRuntimeHeaderWiring
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
variable {t : ℕ}

open ArbitraryWidthHighPreparedRun (input program cost overheadCoefficient changed_bank)

def coefficient : ℕ := max (overheadCoefficient+ArbitraryWidthHighInitializedRunWithin.coefficient 2)
  (2*overheadCoefficient)

theorem runs_within (base : Tapes t prime) (focus : Fin t)
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
    (hf : base.tape focus = sourceWord x) (hhead : base.head focus = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤
      (input base).head j ∧ (input base).head j+
        (coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) :
    HoareWithin (program focus dimensions joined exchange rowsSlot roundedSlot)
      (fun z => z = input base)
      (fun z => z = input (setTape base focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) (cost P e G B jh) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
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
  have ho := ArbitraryWidthHighPreparedRun.overhead_bound P e G B (by rwa [hdvol])
  have hreserve := Nat.mul_le_mul_right (volume prime (originalDescriptor P e G B))
    (show overheadCoefficient+ArbitraryWidthHighInitializedRunWithin.coefficient 2 ≤ coefficient from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume prime (originalDescriptor P e G B))
    (show 2*overheadCoefficient ≤ coefficient from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  have hwp := HoareWithin.of_time_heads hp' lo hi (by
    rintro z rfl j
    have hm := hmargin j
    change lo+_ ≤ (input base).head j ∧ (input base).head j+_ ≤ hi
    dsimp only [V] at ho ⊢
    omega)
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
  have hprepared : ∀ j, lo+(ArbitraryWidthHighInitializedRunWithin.coefficient 2*
      volume prime (originalDescriptor P e G B) : ℕ) ≤
      (ArbitraryWidthHighExecutionInitialize.input caller).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input caller).head j+
        (ArbitraryWidthHighInitializedRunWithin.coefficient 2*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi := by
    intro j
    have ht := hp'.head_change j
    have hm := hmargin j
    change lo+_ ≤ (ArbitraryWidthHighExecutionInitialize.input (ArbitraryWidthHighBranchPrepare.input base)).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input (ArbitraryWidthHighBranchPrepare.input base)).head j+_ ≤ hi at hm
    change lo+_ ≤ (ArbitraryWidthHighExecutionInitialize.input (bank base P G B e r dh jh)).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input (bank base P G B e r dh jh)).head j+_ ≤ hi
    change (input base).head j-(ArbitraryWidthHighBranchPrepare.setupCost prime P G B e V : ℕ) ≤
      (ArbitraryWidthHighExecutionInitialize.input caller).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input caller).head j ≤
        (input base).head j+(ArbitraryWidthHighBranchPrepare.setupCost prime P G B e V : ℕ) at ht
    change lo+_ ≤ (input base).head j ∧ (input base).head j+_ ≤ hi at hm
    change lo+_ ≤ (ArbitraryWidthHighExecutionInitialize.input caller).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input caller).head j+_ ≤ hi
    dsimp only [V] at ht
    omega
  have hbody := ArbitraryWidthHighInitializedRunWithin.runs_within caller (baseSlot focus)
    (exchangeFocus exchange) (movementFocus exchange) (paddingFocus rowsSlot roundedSlot)
    2 P e G B V hP hG hB hV hfit hs rs ss op oe ph rh hh hr hss hop hoe hph hrh
    (exchange_sources base P G B e r dh jh exchange hs rs he)
    (movement_sources base P G B e r dh jh exchange hs rs he)
    (padding_sources base P G B e r dh jh rowsSlot roundedSlot rowBits roundedBits
      rowsTape rowsHead roundedTape roundedHead) bex bmv bpd x
    ((base_cells base P G B e r dh jh focus).2.trans hf)
    ((base_cells base P G B e r dh jh focus).1.trans hhead) le_rfl lo hi hprepared
  rw [changed_bank] at hbody
  let changed := setTape base focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0
  have hc := ArbitraryWidthHighBranchPrepare.cleans dimensions changed
    prime P G B e r (rounded prime e) V Shared50ModularControl.prime_prime.two_le hfit
    hP hG hB hV dh jh dhv dhc jhv jhc bP bG bB be bR
  have hc' := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hc
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime))
    (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime))
    (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
  have hbaseHeads : changed.head = base.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [changed,setTape,Function.update_self,hhead]
    · simp only [changed,setTape,Function.update_of_ne hj]
  have hbHeads := Tapes.append_head_congr _ _ ArbitraryWidthZeroHeaderShared.empty
    ArbitraryWidthZeroHeaderShared.empty
    (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 12) (FixedHeaderBankCopy.empty 12)
      (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) hbaseHeads rfl) rfl) rfl
  have hinputHeads := Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
    (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
    (Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime)
      (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime)
      (Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime)
        (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime) hbHeads rfl) rfl) rfl
  change (input changed).head = (input base).head at hinputHeads
  have hwc := HoareWithin.of_time_post_heads hc' lo hi (by
    rintro z rfl j
    change lo+_ ≤ (input changed).head j ∧ (input changed).head j+_ ≤ hi
    rw [hinputHeads]
    have hm := hmargin j
    dsimp only [V] at ho ⊢
    omega)
  exact ((hwp.seq hbody).seq hwc).consequence (fun _ h => h) (fun _ h => h) (by
    unfold cost
    rfl) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPreparedRunWithin
