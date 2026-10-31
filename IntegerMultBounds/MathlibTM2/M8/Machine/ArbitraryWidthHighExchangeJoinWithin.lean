module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeSharedWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacementWithin

/-! Actual shared-source exchange and ordered joining reuse one ambient
workspace, while the existing endpoint theorem supplies the charged runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
variable {t : ℕ}

open ArbitraryWidthHighExchangeJoin

def coefficient : ℕ := max ArbitraryWidthHighExchangeWithin.coefficient (RadixHighBlockJoinRunWithin.coefficient prime)

theorem realizes_within (caller : Tapes t prime) (focus : Fin t)
    (P e r G B : ℕ) (hfit : r ≤ e) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (hp : (originalDescriptor P e G B).Positive)
    (hv : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hss : Counter.value ss = prime^(e-r)*G) (css : GrowingCounterData.Canonical ss)
    (hop : Counter.value op = P*prime^r) (cop : GrowingCounterData.Canonical op)
    (hoe : Counter.value oe = prime^(e-r)*B) (coe : GrowingCounterData.Canonical oe)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤
      ((caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).head j ∧
      ((caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).head j+
        (coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = (caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (fun w => w = ((setTape caller focus (sourceWord (exchangeJoin P e r G B hfit x)) 0).append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs))
      (ArbitraryWidthHighExchangeJoin.coefficient*(r+1)*volume prime (originalDescriptor P e G B)+1) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let y := ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hfit x
  let ex := ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st
  let mv := ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  let V := volume prime (originalDescriptor P e G B)
  have hEx := Nat.mul_le_mul_right V (show ArbitraryWidthHighExchangeWithin.coefficient ≤ coefficient from le_max_left _ _)
  have hJoin := Nat.mul_le_mul_right V (show RadixHighBlockJoinRunWithin.coefficient prime ≤ coefficient from le_max_right _ _)
  have hex := HoareWithin.extend_heads_eq mv lo hi
    (ArbitraryWidthHighExchangeSharedWithin.realizes_within caller focus (originalDescriptor P e G B)
      hs rs r hp hv hr cr hfit f p node scalar st ready x hf hh lo hi (by
        intro j
        have hm := hmargin (Fin.castAdd movementCount j)
        simp only [Tapes.append,Fin.addCases_left] at hm
        dsimp only [V] at hEx
        simp only [Tapes.append]
        omega))
    (by
      intro j
      have hm := hmargin (Fin.natAdd (t+exchangeCount) j)
      simp only [Tapes.append,Fin.addCases_right] at hm
      dsimp only [mv]
      omega)
  let intermediate := (setTape caller focus (sourceWord y) 0).append ex
  have hcallerHeads : (setTape caller focus (sourceWord y) 0).head = caller.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have hmidHeads : (intermediate.append mv).head = ((caller.append ex).append mv).head :=
    Tapes.append_head_congr _ _ mv mv (Tapes.append_head_congr _ _ ex ex hcallerHeads rfl) rfl
  let z := RadixHighBlockJoinSemantics.reindex
    (ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit)
    (ArbitraryWidthHighExchangeJoinEncoding.encoded y)
  have hm := ArbitraryWidthHighMovementPlacementWithin.join_within intermediate
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
    (by simp only [intermediate,Tapes.append,Fin.addCases_left,setTape,Function.update_self]) lo hi (by
      intro j
      rw [ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hfit,hmidHeads]
      have hh := hmargin j
      dsimp only [ex,mv]
      dsimp only [V] at hJoin
      omega)
  have hfull := hex.seq hm
  apply HoareWithin.of_time_invariant (ArbitraryWidthHighExchangeJoin.realizes_hoare caller focus P e r G B
    hfit hP hG hB hs rs ss op oe hp hv hr cr hss css hop cop hoe coe f p node scalar st ready x hf hh)
  intro c hc
  exact hfull.invariant hc

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinWithin
