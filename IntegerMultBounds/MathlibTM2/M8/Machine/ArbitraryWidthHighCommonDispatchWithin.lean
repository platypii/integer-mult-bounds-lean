module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonDispatchCost
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonHighBodyWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchCompositionWithin


/-! One actual runtime selector chooses the proved high body or elementary
fallback, both on the same bank with identical exact transpose endpoints. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonDispatchWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPrepare (highDepth)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

open ArbitraryWidthHighCommonDispatch

def coefficient (cutoff : ℕ) : ℕ := max (ArbitraryWidthHighCommonDispatchCost.selectorCoefficient cutoff)
  (max ArbitraryWidthHighPreparedRunWithin.coefficient (ArbitraryWidthHighCommonDispatchCost.fallbackCoefficient cutoff))

theorem runs_within (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ highDepth prime n ∧ highDepth prime n < n) (caller : Tapes t prime) (focus : Fin t) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient cutoff*volume prime d : ℕ) ≤ (bank caller d hs).head j ∧
      (bank caller d hs).head j+(coefficient cutoff*volume prime d : ℕ) ≤ hi) :
    HoareWithin (program focus) (fun w => w = bank caller d hs)
      (fun w => w = bank (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs) (cost d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let out := bank (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs
  have hrc := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.rho
  have hec := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.width
  have hfc := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.flag
  have hr := ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2
  have he := ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 3
  have hfl : (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head
      ArbitraryWidthHighCommonSelector.flag = 0 ∧
      (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape
      ArbitraryWidthHighCommonSelector.flag = (fun _ => blank) := by
    simpa only [ArbitraryWidthHighCommonSelector.flag,ArbitraryWidthHighCommonPrepare.output,
      Tapes.append,Fin.addCases_right] using
      ArbitraryWidthHighPrepareShared.private_output_width (a := prime) prime d.width
  have hsel := ArbitraryWidthHighCommonDispatchCost.selector_bound cutoff hcut d hs hp hv
  have hselReserve := Nat.mul_le_mul_right (volume prime d)
    (show ArbitraryWidthHighCommonDispatchCost.selectorCoefficient cutoff ≤ coefficient cutoff from le_max_left _ _)
  have hhighReserve := Nat.mul_le_mul_right (volume prime d)
    (show ArbitraryWidthHighPreparedRunWithin.coefficient ≤ coefficient cutoff from
      (le_max_left _ _).trans (le_max_right _ _))
  have hfallReserve := Nat.mul_le_mul_right (volume prime d)
    (show ArbitraryWidthHighCommonDispatchCost.fallbackCoefficient cutoff ≤ coefficient cutoff from
      (le_max_right _ _).trans (le_max_right _ _))
  have h := ArbitraryWidthHighBranchCompositionWithin.runs_within (rho (t := t)) (ArbitraryWidthHighCommonDispatch.width (t := t)) (flag (t := t))
    (rho_ne_width (t := t)) (rho_ne_flag (t := t)) (width_ne_flag (t := t))
    (highProgram focus) (ArbitraryWidthHighFramedFallback.program focus)
    (bank caller d hs) out out (ArbitraryWidthHighCommonHighBody.cost d hs)
    (ArbitraryWidthHighCommonFallbackBody.cost d)
    (ArbitraryWidthHighPrepare.words prime d.width 2) (hs 3)
    (ArbitraryWidthHighPrepare.words_canonical prime d.width 2)
    (hrc.2.trans (hr.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) (hrc.1.trans hr.1)
    (hec.2.trans (he.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) (hec.1.trans he.1)
    (hfc.2.trans hfl.2) (hfc.1.trans hfl.1)
    lo hi (by intro j; have hm := hmargin j; omega)
    (fun hg => HoareWithin.extend_heads_eq (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount) lo hi
      (ArbitraryWidthHighCommonHighBodyWithin.runs_within caller focus d hs hp hv
        ((guard_values d hs hv).mp hg) x hf hh lo hi (by
          intro j
          have hm := hmargin (Fin.castAdd ArbitraryWidthElementary.tapeCount j)
          simp only [bank,ArbitraryWidthHighFramedFallback.bank,Tapes.append,Fin.addCases_left] at hm
          change lo+_ ≤ (ArbitraryWidthHighCommonHighBody.input caller d hs).head j ∧
            (ArbitraryWidthHighCommonHighBody.input caller d hs).head j+_ ≤ hi
          change lo+_ ≤ (ArbitraryWidthHighCommonHighBody.input caller d hs).head j ∧
            (ArbitraryWidthHighCommonHighBody.input caller d hs).head j+_ ≤ hi at hm
          omega))
      (by
        intro j
        have hm := hmargin (Fin.natAdd _ j)
        simp only [bank,ArbitraryWidthHighFramedFallback.bank,Tapes.append,Fin.addCases_right] at hm
        omega))
    (fun hg => by
      have hw : d.width ≤ cutoff := by
        by_contra hn
        exact hg ((guard_values d hs hv).mpr (hcut d.width (by omega)))
      have hb := ArbitraryWidthHighCommonDispatchCost.fallback_bound cutoff d hp hw
      exact HoareWithin.of_time_heads
        (ArbitraryWidthHighFramedFallback.realizes_hoare caller focus d hs hp hv x hf hh) lo hi (by
          rintro w rfl j
          have hm := hmargin j
          change lo+_ ≤ (bank caller d hs).head j ∧ (bank caller d hs).head j+_ ≤ hi
          omega))
  apply h.consequence (fun _ hh => hh) _ _ (fun _ h => h)
  · intro w hw
    simpa only [ite_self] using hw
  · simp only [cost,guard_values d hs hv,le_refl]

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonDispatchWithin
