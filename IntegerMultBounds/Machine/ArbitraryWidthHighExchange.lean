import IntegerMultBounds.Machine.ArbitraryWidthHighExchangePlacement
import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeSemantics

/-! Actual high-prefix exchange from original canonical headers and rho.
All one-digit views are constructed by SliceRepeat at depth zero; setup,
copying, offset advance, root calls and final descriptor erasure are charged. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchange
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitrarySliceCall (rootCount rootBank data)
open ArbitraryWidthHighExchangePlacement (left_frame aux)
open ArbitraryWidthHighExchangeSemantics (array)

abbrev tapeCount := rootCount+16

def bank (payload : Tapes Shared50NodeSegments.payloadCount prime) (hs : Fin 6 → List Bool)
    (rs : List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) : Tapes tapeCount prime :=
  (rootBank payload hs f p node scalar st).append (ArbitraryWidthHighExchangeControls.input rs)

def initializer := Placement.placed (ArbitraryWidthHighExchangeControls.program (a := prime))
  (finAddFlip : Fin (16+rootCount) ≃ Fin (rootCount+16))
def cleanup := Placement.placed (ArbitraryWidthHighExchangeControls.cleanupProgram (a := prime))
  (finAddFlip : Fin (16+rootCount) ≃ Fin (rootCount+16))
def calls := extend ArbitrarySliceRepeat.consume 2
def program := seq (seq initializer calls) cleanup

def coefficient : ℕ := Shared50RecursiveRootExecution.rootOverhead+
  Shared50RecursiveBudget.base Shared50RecursiveImplementation.returnWidth+1087+128

private theorem zero_budget (V : ℕ) : ArbitrarySliceStepBudget.budget 0 V = (coefficient-128)*V := by
  unfold ArbitrarySliceStepBudget.budget Shared50RecursiveRootExecution.rootBudget Shared50RecursiveBudget.budget coefficient
  rw [Nat.add_sub_cancel]
  ring

/-- Rho can be zero. The original six shape headers and rho survive exactly;
all sixteen private slots except retained rho are blank at head zero. -/
theorem realizes_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (rs : List Bool) (rho : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hr : Counter.value rs = rho) (cr : GrowingCounterData.Canonical rs) (hfit : rho ≤ v.width)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun w => w = bank (data x) hs rs f p node scalar st)
      (fun w => w = bank (data (array v rho hfit x)) hs rs f p node scalar st)
      (coefficient*(rho+1)*volume prime v) := by
  let V := volume prime v
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ V := RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hrV : rho ≤ V := hfit.trans hwV
  let finalOffset := GrowingCounterData.advance (rho*1) (bits 0)
  have ht : Counter.value finalOffset = rho := by
    simp only [finalOffset,GrowingCounterData.advance_value,RecursiveChildQuotientsConstant.bits_value]
    omega
  have ct : GrowingCounterData.Canonical finalOffset := GrowingCounterData.advance_canonical _ _ (RecursiveChildQuotientsConstant.bits_canonical 0)
  have hi := left_frame (ArbitraryWidthHighExchangeControls.initializes (a := prime) rs)
    (rootBank (data x) hs f p node scalar st)
  have hc := ArbitrarySliceRepeat.repeat_hoare 0 v hs (bits 0) (bits 1) rs 0 1 rho hp hv
    (RecursiveChildQuotientsConstant.bits_value 0) (RecursiveChildQuotientsConstant.bits_value 1) hr
    (RecursiveChildQuotientsConstant.bits_canonical 0) (RecursiveChildQuotientsConstant.bits_canonical 1)
    (by simpa using hfit) rfl (by simp) f p node scalar st ready (SharedBank.empty 1 prime)
    (RecursiveViewFrame.free_empty hs) x
  have hm := hoare_extend_eq (ArbitrarySliceRepeat.consume_hoare hc) (aux rs)
  simp only [ArbitrarySliceRepeat.input,ArbitrarySliceRepeat.counted,CountedLoopReuseAlphabet.bank,
    ArbitrarySliceCall.bank,ArbitraryWidthHighExchangePlacement.prepared_bank,
    ArbitraryWidthHighExchangePlacement.returned_bank] at hm
  have he := left_frame (ArbitraryWidthHighExchangeControls.cleans (a := prime) rs finalOffset)
    (rootBank (data (array v rho hfit x)) hs f p node scalar st)
  have hh := (hi.seq hm).seq he
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hcost := ArbitrarySliceRepeat.consumeCost_canonical 0 V 0 1 rho (bits 0) (bits 1) rs
    hV (by omega) (by simpa using hrV)
    (RecursiveChildQuotientsConstant.bits_value 0) (RecursiveChildQuotientsConstant.bits_value 1)
    (RecursiveChildQuotientsConstant.bits_canonical 0) (RecursiveChildQuotientsConstant.bits_canonical 1)
  rw [zero_budget] at hcost
  have wr := GrowingCounterData.canonical_width rs cr
  have wt := GrowingCounterData.canonical_width finalOffset ct
  rw [hr] at wr
  rw [ht] at wt
  have hlog := Nat.log2_le_self rho
  have hcoeff : 128 ≤ coefficient := by unfold coefficient; omega
  have hce : coefficient-128+128 = coefficient := Nat.sub_add_cancel hcoeff
  change _ ≤ coefficient*(rho+1)*V
  conv_rhs => rw [← hce]
  have hscaled := Nat.le_mul_of_pos_right (rho+1) hV
  have hcv := Nat.zero_le ((coefficient-128)*V)
  dsimp only [V] at *
  nlinarith

/-- Exact high-field numeric-address output for the original scalar layout. -/
theorem output_entry (P e rho G B : ℕ) (hr : rho ≤ e)
    (x : Fin (volume prime (ArbitraryWidthHighLayout.originalDescriptor P e G B)) → ZMod 2)
    (a : ArbitraryWidthHighLayout.Coordinate P (prime^rho) (prime^(e-rho)) G B) :
    array (ArbitraryWidthHighLayout.originalDescriptor P e G B) rho hr x
      (ArbitraryWidthHighLayout.originalEquiv prime P e rho G B hr a) =
      x (ArbitraryWidthHighLayout.originalEquiv prime P e rho G B hr (ArbitraryWidthHighLayout.highSwap a)) :=
  ArbitraryWidthHighExchangeSemantics.array_highSwap P e rho G B hr x a

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchange
