import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeJoinEncoding

/-! Paid actual exchange followed by ordered join on one physical caller tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchangeJoin
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeShared (sourceWord)
variable {t : ℕ}

abbrev movementCount := RadixHighBlockJoinSetup.total prime
abbrev exchangeCount := ArbitraryWidthHighExchange.tapeCount

def program (focus : Fin t) := seq
  (extend (ArbitraryWidthHighExchangeShared.program focus) movementCount)
  (ArbitraryWidthHighMovementPlacement.joinProgram (q := prime) (a := prime)
    (Fin.castAdd exchangeCount focus))

def coefficient := ArbitraryWidthHighExchange.coefficient+RadixHighBlockJoinRun.coefficient prime

theorem realizes_hoare (caller : Tapes t prime) (focus : Fin t)
    (P e r G B : ℕ) (hfit : r ≤ e) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (hp : (originalDescriptor P e G B).Positive)
    (hv : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hss : Counter.value ss = prime^(e-r)*G) (css : GrowingCounterData.Canonical ss)
    (hop : Counter.value op = P*prime^r) (cop : GrowingCounterData.Canonical op)
    (hoe : Counter.value oe = prime^(e-r)*B) (coe : GrowingCounterData.Canonical oe)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = (caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (fun w => w = ((setTape caller focus (sourceWord (exchangeJoin P e r G B hfit x)) 0).append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (coefficient*(r+1)*volume prime (originalDescriptor P e G B)+1) := by
  let y := ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hfit x
  let ex := ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st
  let mv := ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  have hex := hoare_extend_eq
    (ArbitraryWidthHighExchangeShared.realizes_hoare caller focus (originalDescriptor P e G B)
      hs rs r hp hv hr cr hfit f p node scalar st ready x hf hh) mv
  let intermediate := (setTape caller focus (sourceWord y) 0).append ex
  let z := RadixHighBlockJoinSemantics.reindex
    (ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit)
    (ArbitraryWidthHighExchangeJoinEncoding.encoded y)
  have hm := ArbitraryWidthHighMovementPlacement.join_hoare intermediate
    (Fin.castAdd exchangeCount focus) r (P*prime^r) (prime^(e-r)*G) (prime^(e-r)*B)
    (fun _ => blank) ss op oe rs z Shared50ModularControl.prime_prime.two_le
    (Nat.mul_pos hP (pow_pos Shared50ModularControl.prime_prime.pos _))
    (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hG)
    (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hB) hss css hop cop hoe coe hr cr
    (by
      simp only [intermediate,Tapes.append,Fin.addCases_left,setTape,Function.update_self]
      exact (ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq y).trans
        (RadixHighBlockJoinLoop.word_reindex
          (ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit)
          (fun _ => blank) (ArbitraryWidthHighExchangeJoinEncoding.encoded y)).symm)
    (by simp only [intermediate,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
  have hout : setTape intermediate (Fin.castAdd exchangeCount focus)
      (RadixHighBlockJoinLoop.word (fun _ => blank)
        (RadixHighBlockJoinSemantics.join prime r (P*prime^r) (prime^(e-r)*G) (prime^(e-r)*B) z)) 0 =
      (setTape caller focus (sourceWord (exchangeJoin P e r G B hfit x)) 0).append ex := by
    dsimp only [intermediate,z,y]
    rw [SharedPlacementAlphabet.setTape_append_left,
      ArbitraryWidthHighExchangeJoinEncoding.join_word,SharedPlacementAlphabet.setTape_setTape]
  rw [hout] at hm
  have hcost := ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit
  have hm' := hm.consequence (fun _ h => h) (fun _ h => h)
    (b' := RadixHighBlockJoinRun.coefficient prime*(r+1)*volume prime (originalDescriptor P e G B))
    (by rw [hcost])
  have h := hex.seq hm'
  apply h.consequence (fun _ h => h) (fun _ h => h)
  unfold coefficient
  ring_nf
  exact le_rfl

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchangeJoin
