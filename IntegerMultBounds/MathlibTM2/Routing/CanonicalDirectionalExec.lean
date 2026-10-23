module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDirectionalBank
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreWrite

/-! Concrete directional execution from blank workspace, including nested
metadata installation and erasure. The input frame is explicit, not generated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def canonicalDirectionalOuterDelimiter {K : ℕ} : Fin (prime + K + 4) :=
  ⟨9, by
    have h := IntegerMultBounds.Networks.two_pow_le_coefficientBound
      (a := 4) (by
        rw [IntegerMultBounds.Networks.coefficientExponent_eq]
        have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) (by decide : 2 ≤ 2 ^ 16)
        exact (by decide : 4 ≤ 2 ^ 2).trans hpow)
    have hp := IntegerMultBounds.Networks.Shared50ModularControl.coefficientBound_lt_prime
    omega⟩

def canonicalDirectionalStream : Fin (canonicalRouterCommonT + 3) :=
  framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (L Lb : ℕ) (rowBits : List Bool) (stages : List (Fin (canonicalRouterStride n)))


local notation "bank" => canonicalDirectionalBank n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages

def canonicalDirectionalCore : Pr Empty (canonicalRouterCommonT + 3) Q (prime + K) Unit :=
  .seq (embProg (canonicalRouterTerminalLift 3) Empty.elim (canonicalTerminalProgram hQ n R B Lb rowBits.length))
    (commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen)

def canonicalDirectionalFrame : List (Fin (prime + K + 4)) :=
  delimitedBankFrames canonicalDirectionalOuterDelimiter
    (framedCoreJobs (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream bank)

def canonicalDirectionalProgram : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  framedCoreCallProgram canonicalDirectionalStream canonicalDirectionalOuterDelimiter
    (fun x => decide (x.val < 9)) Empty.elim
    (canonicalDirectionalCore n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits)

def canonicalDirectionalPrice : ℝ :=
  canonicalTerminalPrice n R B L Lb rowBits.length
    (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).length +
    commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages +
    (6 * (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages).length +
      2 * (framedCoreJobs (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream bank).length + 2 : ℕ)

theorem canonicalDirectional_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) = l.flatten)
    (hinput : S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) =
      canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages ++ rest) :
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages ∧
      Exec Empty.elim (canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits)
        (mk v S) steps (mk v' { S with R := delimitedCallAdvanced S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages) rest (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten }) := by
  unfold canonicalDirectionalProgram canonicalDirectionalPrice canonicalDirectionalFrame
  apply framedCoreCall_exec (N := canonicalRouterCommonT + 3) Empty.elim Empty.elim Empty.elim
    (fun f => f.elim) canonicalDirectionalStream canonicalDirectionalOuterDelimiter
    (fun x => decide (x.val < 9)) (by rfl) bank
    (fun j _ x hx => decide_eq_true (canonicalDirectionalBank_small n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages j x hx))
    rest _ v S hinput ready.tmp ready.blank _ _
  intro u
  dsimp only [embStk]
  have hv : bank canonicalDirectionalStream = l.flatten :=
    canonicalDirectionalBank_stream n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
  have hbank : Function.update bank canonicalDirectionalStream l.flatten = bank :=
    (congrArg (Function.update bank canonicalDirectionalStream) hv.symm).trans
      (Function.update_eq_self _ _)
  have hleft : S.L ∘ framedCoreEmbed (canonicalRouterCommonT + 3) = fun _ => [] := funext ready.left
  rw [hstream, hbank, hleft]
  exact canonicalDirectionalBank_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue S.inp S.out u

/-- The exact post-call state is ready for another direction, with the remaining
input suffix and accumulated archive retained. -/
theorem canonicalDirectional_ready
    (rest : List (Fin (prime + K + 4)))
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) = l.flatten) :
    FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B
      { S with R := delimitedCallAdvanced S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages) rest (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten } := by
  have hr := FramedCoreReady.advance canonicalDirectionalStream S ready
    (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages)
    (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages) rest
  have hout : repairStreamEffect
      (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B l.flatten =
      (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten :=
    (flatten_moveRecs _ l (fun row hr => (hlen row hr).1)).symm
  rw [hstream, hout] at hr
  exact hr

/-- Produce the exact outer directional frame from its live constructed bank.
Generating the bank's scalar and nested input words remains a separate phase. -/
theorem canonicalDirectionalFrameWrite_exec
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (hbank : ∀ j, j ≠ canonicalDirectionalStream →
      S.R (framedCoreEmbed (canonicalRouterCommonT + 3) j) = bank j)
    (htmp : S.R (framedCoreAux (canonicalRouterCommonT + 3) 1) = [])
    (hwork : S.R (framedCoreAux (canonicalRouterCommonT + 3) 2) = []) :
    ∃ v', v'.user = v.user ∧
      configurationWriteCost S.R
        (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream) ≤
        7 * (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages).length + 1 ∧
      Exec Empty.elim (delimitedConfigurationWrite canonicalDirectionalOuterDelimiter
        (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 1)
        (framedCoreAux (canonicalRouterCommonT + 3) 2)
        (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream))
        (mk v S) (configurationWriteCost S.R
          (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream))
        (mk v' { S with R := Function.update S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages ++ S.R (framedCoreAux (canonicalRouterCommonT + 3) 0)) }) := by
  exact framedCoreWrite_exec (N := canonicalRouterCommonT + 3) Empty.elim
    (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream canonicalDirectionalOuterDelimiter
    (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 1)
    (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreAux_nodup (canonicalRouterCommonT + 3))
    (fun j _ => ⟨framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 0,
      framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 1, framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 2⟩)
    bank v S hbank htmp hwork

theorem canonicalDirectionalFrameWriteClean_exec
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (hbank : ∀ j, j ≠ canonicalDirectionalStream →
      S.R (framedCoreEmbed (canonicalRouterCommonT + 3) j) = bank j)
    (htmp : S.R (framedCoreAux (canonicalRouterCommonT + 3) 1) = [])
    (hwork : S.R (framedCoreAux (canonicalRouterCommonT + 3) 2) = []) :
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ 9 * (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages).length + 2 ∧
      Exec Empty.elim (.seq (delimitedConfigurationWrite canonicalDirectionalOuterDelimiter
        (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 1)
        (framedCoreAux (canonicalRouterCommonT + 3) 2)
        (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream))
        (metadataClean (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream)))
        (mk v S) steps
        (mk v' { S with R := Function.update (metadataCleared S.R (framedCoreDestinations (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream)) (framedCoreAux (canonicalRouterCommonT + 3) 0) (canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages ++ S.R (framedCoreAux (canonicalRouterCommonT + 3) 0)) }) := by
  exact framedCoreWriteClean_exec (N := canonicalRouterCommonT + 3) Empty.elim
    (framedCoreEmbed (canonicalRouterCommonT + 3)) (framedCoreEmbed_injective (canonicalRouterCommonT + 3)) canonicalDirectionalStream canonicalDirectionalOuterDelimiter
    (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 1)
    (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreAux_nodup (canonicalRouterCommonT + 3))
    (fun j _ => ⟨framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 0,
      framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 1, framedCoreEmbed_aux (canonicalRouterCommonT + 3) j 2⟩)
    bank v S hbank htmp hwork

end
end IntegerMultBounds.MathlibTM2.Routing
