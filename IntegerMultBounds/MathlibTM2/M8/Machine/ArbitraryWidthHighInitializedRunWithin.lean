module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighInitializedRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRunWithin


/-! The high-width execution from wholly blank private banks: construct all
headers, run the actual high body, and erase every private header afterwards. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighInitializedRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor joinedDescriptor)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPrepare (highDepth rounded)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersCore
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersPadding (paddedWords)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources Bounded)
variable {t : ℕ}

open ArbitraryWidthHighInitializedRun (program cost)

def coefficient (D : ℕ) : ℕ := max (222*D+ArbitraryWidthHighRunWithin.coefficient) (400*D)

theorem runs_within (caller : Tapes t prime) (focus : Fin t)
    (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t) (padding : Fin 10 → Fin t)
    (D P e G B V : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hV : 0 < V)
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
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0)
    (hdom : V ≤ D*volume prime (originalDescriptor P e G B)) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient D*volume prime (originalDescriptor P e G B) : ℕ) ≤
      (ArbitraryWidthHighExecutionInitialize.input caller).head j ∧
      (ArbitraryWidthHighExecutionInitialize.input caller).head j+
        (coefficient D*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) :
    HoareWithin (program focus exchange movement padding)
      (fun w => w = ArbitraryWidthHighExecutionInitialize.input caller)
      (fun w => w = ArbitraryWidthHighExecutionInitialize.input
        (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0))
      (cost V P e G B rh) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have h1 := ArbitraryWidthHighExecutionInitialize.constructs caller exchange movement padding
    hs rs ss op oe ph rh V hV he hm hp be bm bp
  let W := volume prime (originalDescriptor P e G B)
  have hreserve : 222*V+ArbitraryWidthHighRunWithin.coefficient*W ≤ coefficient D*W := by
    calc
      _ ≤ (222*D+ArbitraryWidthHighRunWithin.coefficient)*W := by
        have h := Nat.mul_le_mul_left 222 hdom
        dsimp only [W]
        nlinarith only [h]
      _ ≤ _ := Nat.mul_le_mul_right W (le_max_left _ _)
  have hcleanup : 2*(200*V) ≤ coefficient D*W := by
    calc
      _ ≤ (400*D)*W := by
        have h := Nat.mul_le_mul_left 400 hdom
        dsimp only [W]
        nlinarith only [h]
      _ ≤ _ := Nat.mul_le_mul_right W (le_max_right _ _)
  have hw1 := HoareWithin.of_time_heads h1 lo hi (by
    rintro w rfl j
    have hm := hmargin j
    dsimp only [W] at hreserve
    omega)
  have hprepared : ∀ j, lo+(ArbitraryWidthHighRunWithin.coefficient*W : ℕ) ≤
      (ArbitraryWidthHighExecutionInitialize.output caller hs rs ss op oe ph rh).head j ∧
      (ArbitraryWidthHighExecutionInitialize.output caller hs rs ss op oe ph rh).head j+
        (ArbitraryWidthHighRunWithin.coefficient*W : ℕ) ≤ hi := by
    intro j
    have ht := h1.head_change j
    have hm := hmargin j
    dsimp only [W] at hreserve ⊢
    omega
  have h2 := ArbitraryWidthHighRunWithin.runs_within caller focus P e G B hP hG hB hfit hs rs ss op oe hv
    hr (bm.canonical 4) hss (bm.canonical 0) hop (bm.canonical 1) hoe (bm.canonical 2)
    ph rh hpadding hroot blankTape 0 emptyOne emptyOne emptyTwo RootExecution.blank_ready
    emptyOne (RecursiveViewFrame.free_empty rh) x hf hh lo hi hprepared
  have h3 := ArbitraryWidthHighExecutionInitializeCleanup.cleans
    (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    hs rs ss op oe ph rh V hV be bm bp
  have hcallerHeads : (setTape caller focus
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).head = caller.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have hheads := Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
    (SharedBank.empty ArbitraryWidthHighRun.paddingCount prime)
    (Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime)
      (SharedBank.empty ArbitraryWidthHighExchangeJoin.movementCount prime)
      (Tapes.append_head_congr _ _ (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime)
        (SharedBank.empty ArbitraryWidthHighExchangeJoin.exchangeCount prime) hcallerHeads rfl) rfl) rfl
  change (ArbitraryWidthHighExecutionInitialize.input (setTape caller focus
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)).head =
    (ArbitraryWidthHighExecutionInitialize.input caller).head at hheads
  have hw3 := HoareWithin.of_time_post_heads h3 lo hi (by
    rintro w rfl j
    rw [hheads]
    have hm := hmargin j
    dsimp only [W] at hcleanup
    omega)
  exact ((hw1.seq h2).seq hw3).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighInitializedRunWithin
