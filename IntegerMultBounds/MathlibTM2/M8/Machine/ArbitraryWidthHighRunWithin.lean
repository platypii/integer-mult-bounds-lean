module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceSharedWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighSeparateSharedWithin

/-! Exchange, padded dispatch and separation share one original-volume reserve.
The factor-two row-rounding bound pays the middle phase; all boundary heads
are restored, so no phase-count factor enters workspace. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPrepare (highDepth rounded depth)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
variable {t : ℕ}

open ArbitraryWidthHighRun

def coefficient : ℕ := max ArbitraryWidthHighExchangeJoinWithin.coefficient
  (max (2*ArbitraryWidthPaddedPieceRunWithin.coefficient) (RadixHighBlockSeparateRunWithin.coefficient prime))

theorem runs_within (caller : Tapes t prime) (focus : Fin t) (P e G B : ℕ)
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
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤
      (((caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j ∧
      (((caller.append (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame)).head j+
        (coefficient*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) :
    HoareWithin (program focus)
      (fun w => w = ((caller.append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (fun w => w = (((setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append
        (ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st)).append
        (ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
        (ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame))
      (ArbitraryWidthHighCost.cost 0 P e G B rootHeaders) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let r := highDepth prime e
  let v := joinedDescriptor prime P e r G B
  let ex := ArbitraryWidthHighExchangeShared.privateBank hs rs f p node scalar st
  let mv := ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  let pd := ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders f p node scalar st frame
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,(by change 0 < 1; decide),(by change 0 < 1; decide),hG,hB⟩
  let V := volume prime (originalDescriptor P e G B)
  have hEx := Nat.mul_le_mul_right V
    (show ArbitraryWidthHighExchangeJoinWithin.coefficient ≤ coefficient from le_max_left _ _)
  have hPd := Nat.mul_le_mul_right V
    (show 2*ArbitraryWidthPaddedPieceRunWithin.coefficient ≤ coefficient from
      (le_max_left _ _).trans (le_max_right _ _))
  have hSep := Nat.mul_le_mul_right V
    (show RadixHighBlockSeparateRunWithin.coefficient prime ≤ coefficient from
      (le_max_right _ _).trans (le_max_right _ _))
  have hframe : ∀ j, lo ≤ pd.head j ∧ pd.head j ≤ hi := by
    intro j
    have hm := hmargin (Fin.natAdd (t+exchangeCount+movementCount) j)
    simp only [Tapes.append,Fin.addCases_right] at hm
    dsimp only [pd]
    omega
  have hsetHeads (source : ℤ → Fin (prime+4)) :
      (setTape caller focus source 0).head = caller.head := by
    funext j
    by_cases hj : j = focus
    · subst j; simp only [setTape,Function.update_self,hh]
    · simp only [setTape,Function.update_of_ne hj]
  have h1 := HoareWithin.extend_heads_eq pd lo hi
    (ArbitraryWidthHighExchangeJoinWithin.realizes_within caller focus P e r G B hfit hP hG hB
      hs rs ss op oe hp hv hr cr hss css hop cop hoe coe f p node scalar st ready x hf hh lo hi (by
        intro j
        have hm := hmargin (Fin.castAdd paddingCount j)
        simp only [Tapes.append,Fin.addCases_left] at hm
        dsimp only [V] at hEx
        simp only [Tapes.append]
        omega)) hframe
  let joined := exchangeJoin P e r G B hfit x
  let mid := ((setTape caller focus (sourceWord joined) 0).append ex).append mv
  have hvp : v.Positive := ⟨hP,pow_pos Shared50ModularControl.prime_prime.pos _,
    (by change 0 < 1; decide),hG,hB⟩
  have hR : v.rows ≤ rounded prime e := by
    change prime^(2*r) ≤ rounded prime e
    rw [ArbitraryWidthHighRows.square_power]
    exact ArbitraryWidthHighPrepare.rows_le_rounded prime e Shared50ModularControl.prime_prime.two_le
  have hmidHeads : (mid.append pd).head = (((caller.append ex).append mv).append pd).head :=
    Tapes.append_head_congr _ _ pd pd
      (Tapes.append_head_congr _ _ mv mv (Tapes.append_head_congr _ _ ex ex (hsetHeads _) rfl) rfl) rfl
  have hPadded : ArbitraryWidthPaddedPieceRunWithin.coefficient*volume prime
      (RecursiveRowPadding.withRows v (rounded prime e)) ≤ coefficient*V := by
    have hvol := ArbitraryWidthHighPaddedBudget.volume_le P e G B hfit
    have h := Nat.mul_le_mul_left ArbitraryWidthPaddedPieceRunWithin.coefficient hvol
    change ArbitraryWidthPaddedPieceRunWithin.coefficient*volume prime
      (RecursiveRowPadding.withRows v (rounded prime e)) ≤ _ at h
    calc
      _ ≤ ArbitraryWidthPaddedPieceRunWithin.coefficient*(2*V) := h
      _ = (2*ArbitraryWidthPaddedPieceRunWithin.coefficient)*V := by ring
      _ ≤ _ := hPd
  have h2 := ArbitraryWidthPaddedPieceSharedWithin.runs_within mid
    (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus)) v (rounded prime e) (depth e)
    paddingHeaders rootHeaders hvp hR hpadding hroot
    (ArbitraryWidthHighPaddedBudget.width_fit P e G B)
    (ArbitraryWidthHighPaddedBudget.rows_divisible P e G B)
    f p node scalar st ready frame hfree joined
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
    (by simp only [mid,Tapes.append,Fin.addCases_left,setTape,Function.update_self]) lo hi (by
      intro j
      change lo+_ ≤ (mid.append pd).head j ∧ (mid.append pd).head j+_ ≤ hi
      rw [hmidHeads]
      have hm := hmargin j
      dsimp only [V] at hPadded
      change lo+_ ≤ (((caller.append ex).append mv).append pd).head j ∧
        (((caller.append ex).append mv).append pd).head j+_ ≤ hi at hm
      omega)
  have hout2 : setTape mid (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0 =
      ((setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0).append ex).append mv := by
    dsimp only [mid]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
      SharedPlacementAlphabet.setTape_setTape]
  rw [hout2] at h2
  let low := Shared50RecursiveNodeRows.transpose (one_dvd v.rows) joined
  let sepCaller := (setTape caller focus (sourceWord low) 0).append ex
  have hlowHeads : ((sepCaller.append mv).append pd).head =
      (((caller.append ex).append mv).append pd).head :=
    Tapes.append_head_congr _ _ pd pd
      (Tapes.append_head_congr _ _ mv mv (Tapes.append_head_congr _ _ ex ex (hsetHeads _) rfl) rfl) rfl
  have h3 := HoareWithin.extend_heads_eq pd lo hi
    (ArbitraryWidthHighSeparateSharedWithin.realizes_within sepCaller (Fin.castAdd exchangeCount focus)
      P e r G B hfit hP hG hB rs ss op oe hr cr hss css hop cop hoe coe low
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self])
      (by simp only [sepCaller,Tapes.append,Fin.addCases_left,setTape,Function.update_self]) lo hi (by
        intro j
        have hm := hmargin (Fin.castAdd paddingCount j)
        have he := congrFun hlowHeads (Fin.castAdd paddingCount j)
        simp only [Tapes.append,Fin.addCases_left] at hm he
        dsimp only [V] at hSep
        change lo+_ ≤ (sepCaller.append mv).head j ∧ (sepCaller.append mv).head j+_ ≤ hi
        simp only [Tapes.append]
        rw [he]
        dsimp only [ex,mv] at hm ⊢
        omega)) hframe
  have hout3 : setTape sepCaller (Fin.castAdd exchangeCount focus)
      (sourceWord (separateExchange P e r G B hfit low)) 0 =
      (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append ex := by
    dsimp only [sepCaller,low,joined,v,r]
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_setTape,
      exchange_transpose_separate]
  rw [hout3] at h3
  have h := (h1.seq h2).seq h3
  apply h.consequence (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h)
  unfold ArbitraryWidthHighCost.cost ArbitraryWidthHighCost.movementCoefficient ArbitraryWidthPaddedPieceRun.cost
  change _ ≤ (ArbitraryWidthHighExchangeJoin.coefficient+RadixHighBlockSeparateRun.coefficient prime)*
    (r+1)*volume prime (originalDescriptor P e G B)+
    826*volume prime (RecursiveRowPadding.withRows v (rounded prime e))+
    ArbitraryWidthPieceRun.cost (RecursiveRowPadding.withRows v (rounded prime e)) rootHeaders+
    0*volume prime (originalDescriptor P e G B)+5
  simp only [Nat.add_mul,zero_mul]
  omega

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRunWithin
