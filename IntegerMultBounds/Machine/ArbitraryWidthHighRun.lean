import IntegerMultBounds.Machine.ArbitraryWidthHighCost
import IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceShared

/-! One actual high-width execution: exchange and join, physical row padding,
complete low-width dispatch, physical crop, and final inverse separation.
Every private execution bank is restored. Runtime metadata construction is
separate; no execution callback or recursion-depth oracle enters this proof. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout
open ArbitraryWidthHighPrepare (highDepth rounded depth)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
variable {t : ℕ}

abbrev paddingCount := ArbitraryWidthPaddedPieceRun.tapeCount

def program (focus : Fin t) := seq
  (seq (extend (ArbitraryWidthHighExchangeJoin.program focus) paddingCount)
    (ArbitraryWidthPaddedPieceShared.program
      (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))))
  (extend (ArbitraryWidthHighSeparateShared.program (Fin.castAdd exchangeCount focus)) paddingCount)

theorem runs (caller : Tapes t prime) (focus : Fin t) (P e G B : ℕ)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hfit : highDepth prime e ≤ e)
    (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (hv : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hr : Counter.value rs = highDepth prime e) (cr : GrowingCounterData.Canonical rs)
    (hss : Counter.value ss = prime^(e-highDepth prime e)*G) (css : GrowingCounterData.Canonical ss)
    (hop : Counter.value op = P*prime^(highDepth prime e)) (cop : GrowingCounterData.Canonical op)
    (hoe : Counter.value oe = prime^(e-highDepth prime e)*B) (coe : GrowingCounterData.Canonical oe)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers
      (joinedDescriptor prime P e (highDepth prime e) G B) (rounded prime e) paddingHeaders)
    (hroot : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) rootHeaders)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus)
      (fun w => w = ((caller.append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (fun w => w = (((setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (ArbitraryWidthHighCost.cost 0 P e G B rootHeaders) := by
  let r := highDepth prime e
  let v := joinedDescriptor prime P e r G B
  let ex := ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st
  let mv := ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  let pd := ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,(by change 0 < 1; decide),(by change 0 < 1; decide),hG,hB⟩
  have h1 := hoare_extend_eq
    (ArbitraryWidthHighExchangeJoin.realizes_hoare caller focus P e r G B hfit hP hG hB
      hs rs ss op oe hp hv hr cr hss css hop cop hoe coe f p node scalar st ready x hf hh) pd
  let joined := exchangeJoin P e r G B hfit x
  let mid := ((setTape caller focus (sourceWord joined) 0).append ex).append mv
  have hvp : v.Positive := ⟨hP,pow_pos Shared50ModularControl.prime_prime.pos _,
    (by change 0 < 1; decide),hG,hB⟩
  have hR : v.rows ≤ rounded prime e := by
    change prime^(2*r) ≤ rounded prime e
    rw [ArbitraryWidthHighRows.square_power]
    exact ArbitraryWidthHighPrepare.rows_le_rounded prime e Shared50ModularControl.prime_prime.two_le
  have h2 := ArbitraryWidthPaddedPieceShared.runs mid
    (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus)) v (rounded prime e) (depth e)
    paddingHeaders rootHeaders hvp hR hpadding hroot
    (ArbitraryWidthHighPaddedBudget.width_fit P e G B)
    (ArbitraryWidthHighPaddedBudget.rows_divisible P e G B)
    f p node scalar st ready frame hfree joined
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
  have hout2 : setTape mid (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0 =
      ((setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0).append ex).append mv := by
    dsimp only [mid]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
      SharedPlacementAlphabet.setTape_setTape]
  rw [hout2] at h2
  let low := Shared50RecursiveNodeRows.transpose (one_dvd v.rows) joined
  let sepCaller := (setTape caller focus (sourceWord low) 0).append ex
  have h3 := hoare_extend_eq
    (ArbitraryWidthHighSeparateShared.realizes_hoare sepCaller (Fin.castAdd exchangeCount focus)
      P e r G B hfit hP hG hB rs ss op oe hr cr hss css hop cop hoe coe low
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self])) pd
  have hout3 : setTape sepCaller (Fin.castAdd exchangeCount focus)
      (sourceWord (separateExchange P e r G B hfit low)) 0 =
      (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append ex := by
    dsimp only [sepCaller,low,joined,v,r]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_setTape,
      exchange_transpose_separate]
  rw [hout3] at h3
  have h := (h1.seq h2).seq h3
  apply h.consequence (fun _ h => h) (fun _ h => h)
  unfold ArbitraryWidthHighCost.cost ArbitraryWidthHighCost.movementCoefficient ArbitraryWidthPaddedPieceRun.cost
  change _ ≤ (ArbitraryWidthHighExchangeJoin.coefficient+RadixHighBlockSeparateRun.coefficient prime)*
    (r+1)*volume prime (originalDescriptor P e G B)+
    826*volume prime (RecursiveRowPadding.withRows v (rounded prime e))+
    ArbitraryWidthPieceRun.cost (RecursiveRowPadding.withRows v (rounded prime e)) rootHeaders+
    0*volume prime (originalDescriptor P e G B)+5
  simp only [Nat.add_mul,zero_mul]
  omega

/-- The exact natural runtime used by the physical body retains the original
certified exponent, including all five internal and external sequence edges. -/
theorem cost_bound (P e G B : ℕ) (hs : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (hv : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) hs) :
    (ArbitraryWidthHighCost.cost 0 P e G B hs : ℝ) ≤ ArbitraryWidthHighCost.coefficient 0*
      (volume prime (originalDescriptor P e G B) : ℝ)*(e : ℝ)^Parameters.tau :=
  ArbitraryWidthHighCost.bound 0 P e G B hs hP hG hB hr hv

end
end IntegerMultBounds.Machine.ArbitraryWidthHighRun
