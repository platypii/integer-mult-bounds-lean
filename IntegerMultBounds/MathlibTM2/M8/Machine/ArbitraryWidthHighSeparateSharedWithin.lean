module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighSeparateShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacementWithin

/-! The manuscript's final high-row view inherits the bounded physical inverse
movement, including its exact source word, restored private bank and runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighSeparateSharedWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinEncoding (encoded sourceWord_eq)
variable {t : ℕ}

open ArbitraryWidthHighSeparateShared

theorem realizes_within (caller : Tapes t prime) (focus : Fin t)
    (P e r G B : ℕ) (hfit : r ≤ e) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (rs ss op oe : List Bool)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hss : Counter.value ss = prime^(e-r)*G) (css : GrowingCounterData.Canonical ss)
    (hop : Counter.value op = P*prime^r) (cop : GrowingCounterData.Canonical op)
    (hoe : Counter.value oe = prime^(e-r)*B) (coe : GrowingCounterData.Canonical oe)
    (x : Fin (volume prime (joinedDescriptor prime P e r G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(RadixHighBlockSeparateRunWithin.coefficient prime*volume prime (originalDescriptor P e G B) : ℕ) ≤
      (caller.append (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).head j ∧
      (caller.append (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).head j+
        (RadixHighBlockSeparateRunWithin.coefficient prime*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = caller.append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (fun w => w = (setTape caller focus (sourceWord (separateExchange P e r G B hfit x)) 0).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (RadixHighBlockSeparateRun.coefficient prime*(r+1)*volume prime (originalDescriptor P e G B)) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let z := RadixHighBlockJoinSemantics.reindex
    (ArbitraryWidthHighMovementSemantics.output_volume prime P e r G B) (encoded x)
  have h := ArbitraryWidthHighMovementPlacementWithin.separate_within caller focus r
    (P*prime^r) (prime^(e-r)*G) (prime^(e-r)*B) (fun _ => blank) ss op oe rs z
    Shared50ModularControl.prime_prime.two_le
    (Nat.mul_pos hP (pow_pos Shared50ModularControl.prime_prime.pos _))
    (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hG)
    (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hB)
    hss css hop cop hoe coe hr cr
    (hf.trans ((sourceWord_eq x).trans
      (RadixHighBlockJoinLoop.word_reindex
        (ArbitraryWidthHighMovementSemantics.output_volume prime P e r G B)
        (fun _ => blank) (encoded x)).symm)) hh lo hi (by
      rw [ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit]
      exact hmargin)
  have hout := separate_word P e r G B hfit x
  change RadixHighBlockJoinLoop.word (fun _ => blank) (RadixDigitMoveBlockRows.move z) = _ at hout
  rw [hout] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (by rw [ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit]) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighSeparateSharedWithin
