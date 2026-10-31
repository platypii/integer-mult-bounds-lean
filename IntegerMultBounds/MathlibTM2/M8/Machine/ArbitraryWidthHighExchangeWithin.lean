module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchange
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceRepeatWithin

/-! The high-prefix exchange uses one repeated-slice workspace. Its original
runtime contract supplies the budget; physical boundary runs supply head offsets. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (rootCount rootBank data)
open ArbitraryWidthHighExchangePlacement (left_frame aux)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeSemantics (array)

open ArbitraryWidthHighExchange

def coefficient : ℕ := ArbitrarySliceRepeatWithin.coefficient+40

theorem realizes_within (v : Descriptor) (hs : Fin 6 → List Bool) (rs : List Bool) (rho : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (hr : Counter.value rs = rho) (cr : GrowingCounterData.Canonical rs) (hfit : rho ≤ v.width)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (bank (data x) hs rs f p node scalar st).head j ∧
      (bank (data x) hs rs f p node scalar st).head j+(coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program (fun w => w = bank (data x) hs rs f p node scalar st)
      (fun w => w = bank (data (array v rho hfit x)) hs rs f p node scalar st)
      (ArbitraryWidthHighExchange.coefficient*(rho+1)*volume prime v) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hrV := hfit.trans hwV
  let finalOffset := GrowingCounterData.advance (rho*1) (bits 0)
  have ht : Counter.value finalOffset = rho := by
    simp only [finalOffset,GrowingCounterData.advance_value,RecursiveChildQuotientsConstant.bits_value]
    omega
  have ct : GrowingCounterData.Canonical finalOffset :=
    GrowingCounterData.advance_canonical _ _ (RecursiveChildQuotientsConstant.bits_canonical 0)
  have wr := GrowingCounterData.canonical_width rs cr
  have wt := GrowingCounterData.canonical_width finalOffset ct
  rw [hr] at wr
  rw [ht] at wt
  have hlog := Nat.log2_le_self rho
  have hE : 2*rs.length+29 ≤ 33*volume prime v := by omega
  have hR : 2*finalOffset.length+16 ≤ 20*volume prime v := by omega
  have hiSetup := left_frame (ArbitraryWidthHighExchangeControls.initializes (a := prime) rs)
    (rootBank (data x) hs f p node scalar st)
  have hreserve : 2*rs.length+29+ArbitrarySliceRepeatWithin.coefficient*volume prime v ≤
      coefficient*volume prime v := by
    dsimp only [coefficient]
    nlinarith only [hE,hV]
  have hprepared : ∀ j, lo+(ArbitrarySliceRepeatWithin.coefficient*volume prime v : ℕ) ≤
      ((rootBank (data x) hs f p node scalar st).append (ArbitraryWidthHighExchangeControls.prepared rs)).head j ∧
      ((rootBank (data x) hs f p node scalar st).append (ArbitraryWidthHighExchangeControls.prepared rs)).head j+
        (ArbitrarySliceRepeatWithin.coefficient*volume prime v : ℕ) ≤ hi := by
    intro j
    have hh := hiSetup.head_change j
    have hm := hmargin j
    dsimp only [ArbitraryWidthHighExchange.bank] at hm
    omega
  have hwi := HoareWithin.of_time_heads hiSetup lo hi (by
    rintro input rfl j
    have hm := hmargin j
    dsimp only [ArbitraryWidthHighExchange.bank] at hm
    omega)
  let initial := ArbitrarySliceRepeat.input
    (ArbitrarySliceCall.bank (data x) hs (bits 0) (bits 1) f p node scalar st (SharedBank.empty 1 prime)) rs
  have hview : initial.append (aux rs) =
      (rootBank (data x) hs f p node scalar st).append (ArbitraryWidthHighExchangeControls.prepared rs) :=
    ArbitraryWidthHighExchangePlacement.prepared_bank _ rs
  have hfull : ∀ j, lo+(ArbitrarySliceRepeatWithin.coefficient*volume prime v : ℕ) ≤
      (initial.append (aux rs)).head j ∧
      (initial.append (aux rs)).head j+(ArbitrarySliceRepeatWithin.coefficient*volume prime v : ℕ) ≤ hi := by
    rw [hview]
    exact hprepared
  have hc := ArbitrarySliceRepeatWithin.consume_within 0 v hs (bits 0) (bits 1) rs 0 1 rho hp hv
    (RecursiveChildQuotientsConstant.bits_value 0) (RecursiveChildQuotientsConstant.bits_value 1) hr
    (RecursiveChildQuotientsConstant.bits_canonical 0) (RecursiveChildQuotientsConstant.bits_canonical 1) cr
    (by simpa using hfit) rfl (by simp) f p node scalar st ready (SharedBank.empty 1 prime)
    (RecursiveViewFrame.free_empty hs) x lo hi (by
      intro j
      have hh := hfull (Fin.castAdd 2 j)
      simpa only [Tapes.append,Fin.addCases_left] using hh)
  have hm := HoareWithin.extend_heads_eq (aux rs) lo hi hc (by
    intro j
    have hh := hfull (Fin.natAdd ArbitrarySliceRepeat.tapeCount j)
    simp only [Tapes.append,Fin.addCases_right] at hh
    omega)
  simp only [ArbitrarySliceRepeat.input,ArbitrarySliceRepeat.counted,CountedLoopReuseAlphabet.bank,
    ArbitrarySliceCall.bank,ArbitraryWidthHighExchangePlacement.prepared_bank,
    ArbitraryWidthHighExchangePlacement.returned_bank] at hm
  have he := left_frame (ArbitraryWidthHighExchangeControls.cleans (a := prime) rs finalOffset)
    (rootBank (data (array v rho hfit x)) hs f p node scalar st)
  have hheads : (bank (data (array v rho hfit x)) hs rs f p node scalar st).head =
      (bank (data x) hs rs f p node scalar st).head :=
    Tapes.append_head_congr _ _ _ _
      (ArbitrarySliceCallWithin.rootBank_head_eq (array v rho hfit x) x hs f p node scalar st) rfl
  have hwe := HoareWithin.of_time_post_heads he lo hi (by
    rintro output rfl j
    change lo+(2*(2*finalOffset.length+16) : ℕ) ≤
      (bank (data (array v rho hfit x)) hs rs f p node scalar st).head j ∧
      (bank (data (array v rho hfit x)) hs rs f p node scalar st).head j+
        (2*(2*finalOffset.length+16) : ℕ) ≤ hi
    rw [hheads]
    have hh := hmargin j
    have hb : 2*(2*finalOffset.length+16) ≤ coefficient*volume prime v := by
      dsimp only [coefficient]
      nlinarith only [hR,hV]
    omega)
  have hfullRun := (hwi.seq hm).seq hwe
  apply HoareWithin.of_time_invariant (ArbitraryWidthHighExchange.realizes_hoare
    v hs rs rho hp hv hr cr hfit f p node scalar st ready x)
  intro c hc
  exact hfullRun.invariant hc

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeWithin
